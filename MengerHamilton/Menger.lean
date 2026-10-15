/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import MengerHamilton.MengerCore

/-!
# Menger's theorem

For a finite simple graph `G`:

* `Menger.card_le_of_separates`: if `X` separates `A` from `B` (every walk from `A` to `B` meets
  `X`), any family of pairwise vertex-disjoint `A`–`B` paths has at most `|X|` members.
* `Menger.exists_separator_and_paths`: **Menger (1927), set form.** There are an `A`–`B` separator
  `X` and `|X|` pairwise vertex-disjoint `A`–`B` paths; so the maximum number of disjoint
  `A`–`B` paths equals the minimum size of an `A`–`B` separator.
* `Menger.exists_separator_and_paths_of_not_adj`: **two-vertex form.** For distinct non-adjacent
  `s`, `t` there are a set `X` of vertices other than `s`, `t` meeting every `s`–`t` walk and
  `|X|` `s`–`t` paths, any two of which share only `s` and `t`.
* `Menger.isEdgeReachable_iff`: **edge form.** `u` and `v` stay connected after deleting fewer than
  `k` edges (Mathlib's `IsEdgeReachable`) if and only if there are `k` pairwise edge-disjoint
  `u`–`v` paths.
* `Menger.isEdgeConnected_iff`: **global edge form.** `G` is `k`-edge-connected
  (Mathlib's `IsEdgeConnected`) if and only if any two vertices are joined by `k` pairwise
  edge-disjoint paths.
-/

@[expose] public section

open SimpleGraph

namespace Menger

variable {V : Type*}

/-- `X` separates `A` from `B` in `G`: every walk from a vertex of `A` to a vertex of `B` passes
through a vertex of `X`. -/
def Separates (G : SimpleGraph V) (A B X : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ x ∈ X, x ∈ p.support

/-- **Weak duality.** Pairwise vertex-disjoint `A`–`B` paths are at most as many as the vertices
of any `A`–`B` separator. -/
theorem card_le_of_separates {G : SimpleGraph V} {A B X : Finset V}
    (hX : Separates G A B X) {m : ℕ} (a b : Fin m → V) (p : ∀ i, G.Walk (a i) (b i))
    (hA : ∀ i, a i ∈ A) (hB : ∀ i, b i ∈ B)
    (hdisj : ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∉ (p j).support) :
    m ≤ X.card := by
  classical
  have h : ∀ i, ∃ x ∈ X, x ∈ (p i).support := fun i => hX _ (hA i) _ (hB i) (p i)
  choose f hfX hfp using h
  have hinj : Set.InjOn f ((Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    intro i _ j _ hij
    by_contra hne
    exact hdisj i j hne _ (hfp i) (by rw [hij]; exact hfp j)
  simpa using Finset.card_le_card_of_injOn f (fun i _ => hfX i) hinj

/-- **Menger's theorem (1927), set form.** In a finite graph there are an `A`–`B` separator `X`
and `|X|` pairwise vertex-disjoint paths from `A` to `B`. -/
theorem exists_separator_and_paths [Finite V] (G : SimpleGraph V)
    (A B : Finset V) :
    ∃ X : Finset V, Separates G A B X ∧
      ∃ (a b : Fin X.card → V) (p : ∀ i, G.Walk (a i) (b i)),
        (∀ i, a i ∈ A ∧ b i ∈ B ∧ (p i).IsPath) ∧
        ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∉ (p j).support := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨X, hXmem, hXmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun X : Finset V => Separates G A B X)) Finset.card
    ⟨A, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun a ha b _ p => ⟨a, ha, p.start_mem_support⟩⟩⟩
  rw [Finset.mem_filter] at hXmem
  obtain ⟨P, hP, hd⟩ := Aux.fam_of_le _ G rfl A B X.card
    (fun Z hZ => hXmin Z (Finset.mem_filter.2 ⟨Finset.mem_univ _, hZ⟩))
  exact ⟨X, hXmem.2, fun i => (P i).1, fun i => (P i).2.1, fun i => (P i).2.2,
    fun i => ⟨(hP i).1, (hP i).2.1, (hP i).2.2.1⟩, hd⟩

/-- **Menger's theorem, two-vertex form.** For distinct non-adjacent vertices `s`, `t` of a finite
graph there are a set `X` of vertices other than `s` and `t` meeting every `s`–`t` walk and `|X|`
paths from `s` to `t`, any two of which share only `s` and `t`. -/
theorem exists_separator_and_paths_of_not_adj [Finite V] (G : SimpleGraph V)
    {s t : V} (hst : s ≠ t) (hadj : ¬ G.Adj s t) :
    ∃ X : Finset V, s ∉ X ∧ t ∉ X ∧ (∀ p : G.Walk s t, ∃ x ∈ X, x ∈ p.support) ∧
      ∃ p : Fin X.card → G.Walk s t, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∈ (p j).support → x = s ∨ x = t := by
  classical
  have := Fintype.ofFinite V
  set H := G.deleteEdges {e | s ∈ e ∨ t ∈ e} with hH
  set A := G.neighborFinset s with hA
  set B := G.neighborFinset t with hB
  have hHs : ∀ w, ¬ H.Adj s w := by intro w h; simp [hH] at h
  have hHt : ∀ w, ¬ H.Adj t w := by intro w h; simp [hH] at h
  have hsA : s ∉ A := by simp [hA]
  have htA : t ∉ A := by simpa [hA] using hadj
  have hnot : ∀ {a b : V} (q : H.Walk a b), a ∈ A → s ∉ q.support ∧ t ∉ q.support := by
    intro a b q ha
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact hsA (Aux.start_eq_of_isolated hHs q h ▸ ha)
    · exact htA (Aux.start_eq_of_isolated hHt q h ▸ ha)
  obtain ⟨X, hX, a, b, p, hp, hd⟩ := exists_separator_and_paths H A B
  have herase : ∀ v, v ∈ X → (v = s ∨ v = t) → False := by
    intro v hv hvst
    have hsep' : Separates H A B (X.erase v) := by
      intro a' ha' b' hb' q
      obtain ⟨x, hx, hxq⟩ := hX a' ha' b' hb' q
      refine ⟨x, Finset.mem_erase.2 ⟨?_, hx⟩, hxq⟩
      rintro rfl
      rcases hvst with rfl | rfl
      · exact (hnot q ha').1 hxq
      · exact (hnot q ha').2 hxq
    have := card_le_of_separates hsep' a b p (fun i => (hp i).1) (fun i => (hp i).2.1) hd
    rw [Finset.card_erase_of_mem hv] at this
    have : 0 < X.card := Finset.card_pos.2 ⟨v, hv⟩
    omega
  refine ⟨X, fun h => herase s h (Or.inl rfl), fun h => herase t h (Or.inr rfl), ?_, ?_⟩
  · have key : ∀ {u v : V} (q : G.Walk u v), v = t →
        (u = s ∨ ∃ a ∈ A, ∃ r : H.Walk a u, ∀ w ∈ r.support, w ∉ X) →
        (∀ w ∈ q.support, w ∉ X) → False := by
      intro u v q
      induction q with
      | nil =>
        rintro rfl (h | ⟨a', ha', r, hr⟩) -
        · exact hst h.symm
        · have := Aux.start_eq_of_isolated hHt r r.end_mem_support
          subst this
          exact htA ha'
      | @cons u w v h q ih =>
        rintro rfl hu hq
        apply ih rfl ?_ (fun x hx => hq x (by simp [hx]))
        have hwX : w ∉ X := hq w (by simp)
        by_cases hws : w = s
        · exact Or.inl hws
        rcases hu with rfl | ⟨a', ha', r, hr⟩
        · exact Or.inr ⟨w, by simpa [hA] using h, Walk.nil, by simpa using hwX⟩
        · have hus : u ≠ s := fun hus => (hnot r ha').1 (hus ▸ r.end_mem_support)
          have hut : u ≠ v := fun hut => (hnot r ha').2 (hut ▸ r.end_mem_support)
          by_cases hwt : w = v
          · subst hwt
            obtain ⟨x, hx, hxr⟩ := hX a' ha' u (by simpa [hB] using h.symm) r
            exact (hr x hxr hx).elim
          · have hadjH : H.Adj u w := by
              simp only [hH, deleteEdges_adj, Set.mem_ofPred_eq, Sym2.mem_iff, not_or]
              exact ⟨h, ⟨Ne.symm hus, Ne.symm hws⟩, Ne.symm hut, Ne.symm hwt⟩
            refine Or.inr ⟨a', ha', r.concat hadjH, fun x hx => ?_⟩
            rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hr x hx
            · exact hwX
    intro q
    by_contra hcon
    push Not at hcon
    exact key q rfl (Or.inl rfl) (fun w hw hwX => hcon w hwX hw)
  · have hle : H ≤ G := G.deleteEdges_le _
    have hsa : ∀ i, G.Adj s (a i) := fun i => by simpa [hA] using (hp i).1
    have hbt : ∀ i, G.Adj (b i) t := fun i => (by simpa [hB] using (hp i).2.1 : G.Adj t (b i)).symm
    refine ⟨fun i => Walk.cons (hsa i) (((p i).mapLe hle).concat (hbt i)), fun i => ?_,
      fun i j hij x hx hx' => ?_⟩
    · have h1 := hnot (p i) (hp i).1
      refine Walk.IsPath.cons (((hp i).2.2.mapLe hle).concat ?_ _) ?_
      · simpa using h1.2
      · simp only [Walk.support_concat, Walk.support_mapLe_eq_support, List.mem_append,
          List.mem_singleton, not_or]
        exact ⟨h1.1, hst⟩
    · simp only [Walk.support_cons, Walk.support_concat, Walk.support_mapLe_eq_support,
        List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx hx'
      rcases hx with h | h | h
      · exact Or.inl h
      · rcases hx' with h' | h' | h'
        · exact Or.inl h'
        · exact absurd h' (hd i j hij x h)
        · exact Or.inr h'
      · exact Or.inr h

/-- **Menger's theorem, edge form.** In a finite graph, `u` and `v` remain connected after the
deletion of any fewer than `k` edges if and only if there are `k` pairwise edge-disjoint paths
from `u` to `v`. -/
theorem isEdgeReachable_iff [Finite V] (G : SimpleGraph V) (k : ℕ) (u v : V) :
    G.IsEdgeReachable k u v ↔
      ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges := by
  constructor
  · intro h
    by_cases huv : u = v
    · subst huv
      exact ⟨fun _ => Walk.nil, fun _ => Walk.IsPath.nil, fun _ _ _ => by simp⟩
    classical
    have := Fintype.ofFinite V
    obtain ⟨X, hX, a, b, P, hP, hd⟩ := exists_separator_and_paths G.lineGraph
      (Finset.univ.filter (fun e : G.edgeSet => u ∈ (e : Sym2 V)))
      (Finset.univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V)))
    have hk : k ≤ X.card := by
      by_contra hlt
      push Not at hlt
      have hS : (Subtype.val '' (X : Set G.edgeSet)).encard < k := by
        rw [Subtype.val_injective.encard_image, Set.encard_coe_eq_coe_finsetCard]
        exact_mod_cast hlt
      obtain ⟨q⟩ := h hS
      obtain ⟨w, hadj, q', -⟩ := Walk.exists_eq_cons_of_ne huv q
      rw [deleteEdges_adj] at hadj
      obtain ⟨e', he'v, r, hr⟩ := Aux.lift_to_lineGraph (q'.mapLe (G.deleteEdges_le _))
        ⟨s(u, w), hadj.1⟩ (Sym2.mem_mk_right _ _)
      obtain ⟨x, hxX, hxr⟩ := hX ⟨s(u, w), hadj.1⟩ (by simp) e' (by simp [he'v]) r
      rcases hr x hxr with rfl | hx
      · exact hadj.2 ⟨_, hxX, rfl⟩
      · rw [Walk.edges_mapLe_eq_edges] at hx
        have := q'.edges_subset_edgeSet hx
        rw [edgeSet_deleteEdges] at this
        exact this.2 ⟨x, hxX, rfl⟩
    have hlow : ∀ i, ∃ r : G.Walk u v, ∀ g ∈ r.edges, ∃ e'' ∈ (P i).support, g = (e'' : Sym2 V) :=
      fun i => Aux.lower_from_lineGraph (P i) (by simpa using (hP i).1) (by simpa using (hP i).2.1)
    choose r hr using hlow
    refine ⟨fun i => (r (Fin.castLE hk i)).bypass, fun i => Walk.bypass_isPath _,
      fun i j hij g hg hg' => ?_⟩
    obtain ⟨e1, he1, rfl⟩ := hr _ g (Walk.edges_bypass_subset_edges _ hg)
    obtain ⟨e2, he2, he12⟩ := hr _ _ (Walk.edges_bypass_subset_edges _ hg')
    have := Subtype.ext he12
    subst this
    exact hd _ _ (fun h => hij (Fin.castLE_injective hk h)) _ he1 he2
  · rintro ⟨p, hp, hd⟩ S hS
    by_contra hreach
    have hmeet : ∀ i, ∃ e ∈ (p i).edges, e ∈ S := by
      intro i
      by_contra h
      push Not at h
      exact hreach ⟨(p i).toDeleteEdges S h⟩
    choose f hf hfS using hmeet
    have hinj : Set.InjOn f Set.univ := by
      intro i _ j _ hij
      by_contra hne
      exact hd i j hne (hf i) (by rw [hij]; exact hf j)
    have := Set.encard_le_encard_of_injOn (fun i _ => hfS i) hinj
    simp only [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] at this
    exact absurd hS (not_lt.2 this)

/-- **Menger's theorem, global edge form.** A finite graph is `k`-edge-connected if and only if any
two vertices are joined by `k` pairwise edge-disjoint paths. -/
theorem isEdgeConnected_iff [Finite V] (G : SimpleGraph V) (k : ℕ) :
    G.IsEdgeConnected k ↔
      ∀ u v : V, ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges := by
  exact ⟨fun h u v => (isEdgeReachable_iff G k u v).1 (h u v),
    fun h u v => (isEdgeReachable_iff G k u v).2 (h u v)⟩

end Menger
