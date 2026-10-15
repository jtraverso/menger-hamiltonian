/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MengerHamilton.LongerCycle

/-!
# Auxiliary material for the Chvátal–Erdős theorem

* `exists_fan`: the fan lemma, derived from Menger's theorem: in a graph that stays connected after
  deleting fewer than `k` vertices, a vertex `x` off a cycle `C` is joined to `C` by at least
  `min k |C|` paths sharing only `x`, each meeting `C` only at its last vertex.
* `exists_cycArr_of_conn`: such a graph (with `k ≥ 2`) contains a cycle.
* `chvatal_erdos_aux`: the Chvátal–Erdős theorem, via a longest cycle.
-/

@[expose] public section

open SimpleGraph

namespace Hamiltonicity

variable {V : Type*}

lemma CycArr.ne_succ {G : SimpleGraph V} {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) (i : ℕ) :
    f i ≠ f (i + 1) := by
  intro h
  rw [hC.eq_iff] at h
  have hm := hC.three_le
  have hlt : i % m < m := Nat.mod_lt _ hC.pos
  by_cases hc : i % m + 1 < m
  · rw [CycArr.succ_mod_of_lt hc] at h
    omega
  · rw [CycArr.succ_mod_of_eq (by omega)] at h
    omega

/-- Truncate a path ending in `B` at its first vertex in `B`. -/
lemma exists_trunc {H : SimpleGraph V} (B : Set V) : ∀ {a b : V} (p : H.Walk a b), b ∈ B →
    p.IsPath → ∃ b' ∈ B, ∃ p' : H.Walk a b', p'.IsPath ∧ p'.support ⊆ p.support ∧
      ∀ y ∈ p'.support, y ∈ B → y = b'
  | _, _, .nil, hb, _ => ⟨_, hb, .nil, Walk.IsPath.nil, fun _ h => h, by simp⟩
  | a, _, .cons h q, hb, hp => by
    by_cases ha : a ∈ B
    · exact ⟨a, ha, .nil, Walk.IsPath.nil, by simp, by simp⟩
    · rw [Walk.cons_isPath_iff] at hp
      obtain ⟨b', hb', q', hq', hsub, hlast⟩ := exists_trunc B q hb hp.1
      refine ⟨b', hb', .cons h q', ?_, ?_, ?_⟩
      · rw [Walk.cons_isPath_iff]
        exact ⟨hq', fun h' => hp.2 (hsub h')⟩
      · simp only [Walk.support_cons]
        exact List.cons_subset_cons _ hsub
      · intro y hy hyB
        rw [Walk.support_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact absurd hyB ha
        · exact hlast y hy hyB

/-- If `G - S` is connected, two vertices outside `S` are joined by a path avoiding `S`. -/
lemma exists_path_avoiding {G : SimpleGraph V} (S : Set V) (hS : (G.induce Sᶜ).Connected)
    {a b : V} (ha : a ∉ S) (hb : b ∉ S) :
    ∃ p : G.Walk a b, p.IsPath ∧ ∀ y ∈ p.support, y ∉ S := by
  classical
  obtain ⟨w⟩ := hS.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨(w.map (Embedding.induce Sᶜ).toHom).bypass, Walk.bypass_isPath _, fun y hy => ?_⟩
  have := Walk.support_bypass_subset_support _ hy
  erw [Walk.support_map, List.mem_map] at this
  obtain ⟨z, -, rfl⟩ := this
  exact z.2

/-- **Fan lemma.** -/
lemma exists_fan [Finite V] {G : SimpleGraph V} {k : ℕ}
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected)
    {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) {x : V} (hx : ∀ i, f i ≠ x) :
    ∃ r, min k m ≤ r ∧ ∃ (t : Fin r → ℕ) (P : ∀ j, G.Walk x (f (t j))),
      (∀ j, (P j).IsPath) ∧ (∀ j, ∀ y ∈ (P j).support, ∀ i, f i = y → y = f (t j)) ∧
      (∀ i j, i ≠ j → ∀ y ∈ (P i).support, y ∈ (P j).support → y = x) := by
  classical
  have := Fintype.ofFinite V
  set H := G.deleteEdges {e | x ∈ e} with hH
  have hHx : ∀ w, ¬ H.Adj x w := by intro w h; simp [hH] at h
  have hle : H ≤ G := G.deleteEdges_le _
  set A := G.neighborFinset x with hA
  set B := (Finset.range m).image f with hB
  have hfB : ∀ i, f i ∈ B := fun i => by
    rw [hC.eq_mod i]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.mod_lt _ hC.pos))
  have hBf : ∀ y ∈ B, ∃ i, f i = y := by
    intro y hy
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hy
    exact ⟨i, hi⟩
  have hBcard : B.card = m := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact hC.inj i j (by simpa using hi) (by simpa using hj) hij
  have hxA : x ∉ A := by simp [A]
  obtain ⟨X, hX, a, b, p, hp, hd⟩ := Menger.exists_separator_and_paths H A B
  refine ⟨X.card, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have hXk : X.card < k := lt_of_lt_of_le hlt (min_le_left _ _)
    have hXm : X.card < m := lt_of_lt_of_le hlt (min_le_right _ _)
    obtain ⟨β, hβB, hβX⟩ : ∃ β ∈ B, β ∉ X := by
      by_contra hcon
      push Not at hcon
      have := Finset.card_le_card (show B ⊆ X from hcon)
      omega
    obtain ⟨i0, hi0⟩ := hBf β hβB
    set S : Set V := ↑(X.erase x) with hS
    have hSk : S.ncard < k := by
      rw [hS, Set.ncard_coe_finset]
      exact lt_of_le_of_lt (Finset.card_erase_le) hXk
    have hxS : x ∉ S := by simp [S]
    have hβS : β ∉ S := by simp [S, hβX]
    obtain ⟨w, hw, hwS⟩ := exists_path_avoiding S (hconn S hSk) hxS hβS
    have hxβ : x ≠ β := fun h => hx i0 (hi0.trans h.symm)
    obtain ⟨a', hxa', rest, rfl⟩ := Walk.exists_eq_cons_of_ne hxβ w
    rw [Walk.cons_isPath_iff] at hw
    have hrest : ∀ e ∈ rest.edges, e ∉ {e : Sym2 V | x ∈ e} := by
      intro e he hxe
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 hxe
      exact hw.2 (rest.fst_mem_support_of_mem_edges he)
    obtain ⟨z, hzX, hzr⟩ := hX a' (by simpa [A] using hxa') β hβB
      (rest.toDeleteEdges {e | x ∈ e} hrest)
    have hzr' : z ∈ rest.support := by
      simp only [Walk.toDeleteEdges] at hzr
      rwa [Walk.support_transfer] at hzr
    have hzx : z ≠ x := fun h => hw.2 (h ▸ hzr')
    exact hwS z (by simp [hzr']) (by simp [S, hzX, hzx])
  · have htr : ∀ i, ∃ b' ∈ (B : Set V), ∃ p' : H.Walk (a i) b', p'.IsPath ∧
        p'.support ⊆ (p i).support ∧ ∀ y ∈ p'.support, y ∈ (B : Set V) → y = b' :=
      fun i => exists_trunc (B : Set V) (p i) (hp i).2.1 (hp i).2.2
    choose b' hb' p' hp' hsub hlast using htr
    have hpos : ∀ i, ∃ t, f t = b' i := fun i => hBf _ (hb' i)
    choose t ht using hpos
    have hxp : ∀ i, x ∉ (p' i).support := by
      intro i hxi
      have := Menger.Aux.start_eq_of_isolated hHx (p' i) hxi
      exact hxA (this ▸ (hp i).1)
    have hadjx : ∀ i, G.Adj x (a i) := fun i => by simpa [A] using (hp i).1
    let P : ∀ i, G.Walk x (f (t i)) := fun i =>
      (Walk.cons (hadjx i) ((p' i).mapLe hle)).copy rfl (ht i).symm
    refine ⟨t, P, fun i => ?_, fun i y hy j hj => ?_, fun i j hij y hyi hyj => ?_⟩
    · simp only [P, Walk.isPath_copy, Walk.cons_isPath_iff, Walk.support_mapLe_eq_support]
      exact ⟨(hp' i).mapLe hle, hxp i⟩
    · simp only [P, Walk.support_copy, Walk.support_cons, Walk.support_mapLe_eq_support,
        List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact absurd hj (hx j)
      · rw [ht i]
        exact hlast i y hy (by rw [← hj]; exact hfB j)
    · simp only [P, Walk.support_copy, Walk.support_cons, Walk.support_mapLe_eq_support,
        List.mem_cons] at hyi hyj
      rcases hyi with rfl | hyi
      · rfl
      rcases hyj with rfl | hyj
      · rfl
      exact absurd (hsub j hyj) (hd i j hij y (hsub i hyi))

/-- A graph on at least three vertices that stays connected after deleting fewer than `k ≥ 2`
vertices contains a cycle. -/
lemma exists_cycArr_of_conn [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hn : 3 ≤ Fintype.card V) (hk2 : 2 ≤ k)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) :
    ∃ m f, CycArr G m f := by
  classical
  by_contra hno
  push Not at hno
  have hacyc : G.IsAcyclic := fun v c hc => hno _ _ (cycArr_of_isCycle hc)
  have hconnG : G.Connected := by
    have hc0 := hconn ∅ (by simp; omega)
    have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    refine ⟨fun a b => ?_⟩
    obtain ⟨p, -, -⟩ := exists_path_avoiding ∅ hc0 (Set.notMem_empty a) (Set.notMem_empty b)
    exact p.reachable
  have htree : G.IsTree := ⟨hconnG, hacyc⟩
  have hdeg : ∀ v, 2 ≤ G.degree v := by
    intro v
    by_contra hlt
    push Not at hlt
    set N := G.neighborFinset v with hN
    have hNk : (N : Set V).ncard < k := by
      rw [Set.ncard_coe_finset, card_neighborFinset_eq_degree]
      omega
    obtain ⟨w, hw⟩ : ∃ w, w ∉ insert v N := by
      by_contra hcon
      push Not at hcon
      have := Finset.card_le_card (show Finset.univ ⊆ insert v N from fun w _ => hcon w)
      rw [Finset.card_univ] at this
      have := Finset.card_insert_le v N
      rw [card_neighborFinset_eq_degree] at this
      omega
    simp only [Finset.mem_insert, not_or] at hw
    have hvN : v ∉ (N : Set V) := by simp [N]
    obtain ⟨p, -, hpS⟩ := exists_path_avoiding _ (hconn _ hNk) hvN (by simpa using hw.2)
    obtain ⟨w', hvw', q, rfl⟩ := Walk.exists_eq_cons_of_ne (Ne.symm hw.1) p
    exact hpS w' (by simp) (by simpa [N] using hvw')
  have h1 := htree.card_edgeFinset
  have h2 := G.sum_degrees_eq_twice_card_edges
  have h3 : ∑ _v : V, 2 ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => hdeg v
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h3
  omega

/-- **Chvátal–Erdős**, with `k`-connectivity unfolded. -/
lemma chvatal_erdos_aux [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V) (k : ℕ)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected)
    (hα : ∀ s : Set V, G.IsIndepSet s → s.ncard ≤ k) : G.IsHamiltonian := by
  classical
  by_cases hall : ∀ u v, u ≠ v → G.Adj u v
  · exact isHamiltonian_of_forall_adj hn hall
  push Not at hall
  obtain ⟨s, t, hst, hnst⟩ := hall
  have hk2 : 2 ≤ k := by
    have := hα {s, t} (by
      intro a ha b hb hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hnst
      · exact fun h => hnst h.symm
      · exact absurd rfl hab)
    rwa [Set.ncard_pair hst] at this
  obtain ⟨m0, f0, hf0⟩ := exists_cycArr_of_conn hn hk2 hconn
  -- a longest cycle
  set M := Nat.findGreatest (fun m => ∃ f, CycArr G m f) (Fintype.card V) with hM
  obtain ⟨f, hf⟩ : ∃ f, CycArr G M f :=
    Nat.findGreatest_spec (P := fun m => ∃ f, CycArr G m f) hf0.le_card ⟨f0, hf0⟩
  have hmax : ∀ m' g, CycArr G m' g → m' ≤ M := fun m' g hg =>
    Nat.le_findGreatest (P := fun m => ∃ f, CycArr G m f) hg.le_card ⟨g, hg⟩
  by_cases hMn : M = Fintype.card V
  · exact hf.isHamiltonian hMn
  have hMlt : M < Fintype.card V := lt_of_le_of_ne hf.le_card hMn
  have hM3 := hf.three_le
  -- a vertex off the cycle
  obtain ⟨x, hx⟩ : ∃ x, ∀ i, f i ≠ x := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset V) ⊆ (Finset.range M).image f := by
      intro y _
      obtain ⟨i, hi⟩ := hcon y
      rw [hf.eq_mod] at hi
      exact Finset.mem_image.2 ⟨_, Finset.mem_range.2 (Nat.mod_lt _ hf.pos), hi⟩
    have h1 := Finset.card_le_card hsub
    have h2 := (Finset.card_image_le (s := Finset.range M) (f := f)).trans_eq
      (Finset.card_range M)
    rw [Finset.card_univ] at h1
    omega
  obtain ⟨r, hr, t, P, hP, hPint, hPdisj⟩ := exists_fan hconn hf hx
  have hPlen : ∀ j, 1 ≤ (P j).length := fun j => by
    by_contra h
    push Not at h
    exact hx _ (Walk.eq_of_length_eq_zero (by omega : (P j).length = 0)).symm
  have hlonger : ∀ a b (Q : G.Walk (f a) (f b)), f a ≠ f b → Q.IsPath → 2 ≤ Q.length →
      (∀ y ∈ Q.support, ∀ i, f i = y → y = f a ∨ y = f b) → G.Adj (f (a + 1)) (f (b + 1)) →
      False := by
    intro a b Q hab hQ hQl hint hadj
    obtain ⟨g, hg⟩ := hf.extend hab Q hQ hQl hint hadj
    have := hmax _ _ hg
    omega
  have hxtail : ∀ j, x ∉ (P j).support.tail := by
    intro j hxj
    have := (hP j).support_nodup
    rw [← Walk.cons_tail_support] at this
    exact (List.nodup_cons.1 this).1 hxj
  have htinj : ∀ i j, f (t i) = f (t j) → i = j := by
    intro i j h
    by_contra hij
    exact hx _ (hPdisj i j hij _ (P i).end_mem_support (by rw [h]; exact (P j).end_mem_support))
  -- two fan paths joined at `x`
  have hcomb : ∀ i j, i ≠ j → G.Adj (f (t i + 1)) (f (t j + 1)) → False := by
    intro i j hij hadj
    have hne : f (t i) ≠ f (t j) := fun h => hij (htinj i j h)
    refine hlonger (t i) (t j) ((P i).reverse.append (P j)) hne ?_ ?_ ?_ hadj
    · rw [Walk.isPath_def, Walk.support_append, Walk.support_reverse, List.nodup_append]
      refine ⟨List.nodup_reverse.2 (hP i).support_nodup,
        (hP j).support_nodup.sublist (List.tail_sublist _), ?_⟩
      intro y hy z hz hyz
      subst hyz
      rw [List.mem_reverse] at hy
      have := hPdisj i j hij y hy (List.mem_of_mem_tail hz)
      subst this
      exact hxtail j hz
    · rw [Walk.length_append, Walk.length_reverse]
      have := hPlen i
      have := hPlen j
      omega
    · intro y hy i' hi'
      rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hy
      rcases hy with hy | hy
      · exact Or.inl (hPint i y hy i' hi')
      · exact Or.inr (hPint j y hy i' hi')
  -- no two consecutive endpoints
  have hnc : ∀ i j, f (t j) ≠ f (t i + 1) := by
    intro i j h
    by_cases hij : i = j
    · subst hij
      exact hf.ne_succ _ h
    · apply hcomb i j hij
      rw [← h]
      exact hf.adj _
  -- `x` is not adjacent to a successor
  have hxs : ∀ i, ¬ G.Adj x (f (t i + 1)) := by
    intro i hadj
    have hne : f (t i) ≠ f (t i + 1) := hf.ne_succ _
    have hnot : f (t i + 1) ∉ (P i).support := fun h => hne (hPint i _ h _ rfl).symm
    refine hlonger (t i) (t i + 1) ((P i).reverse.concat hadj) hne ?_ ?_ ?_ (hf.adj _)
    · rw [Walk.isPath_def, Walk.support_concat, Walk.support_reverse,
        List.nodup_append]
      refine ⟨List.nodup_reverse.2 (hP i).support_nodup, List.nodup_singleton _, ?_⟩
      intro y hy z hz hyz
      rw [List.mem_singleton] at hz
      subst hz hyz
      exact hnot (List.mem_reverse.1 hy)
    · rw [Walk.length_concat, Walk.length_reverse]
      have := hPlen i
      omega
    · intro y hy i' hi'
      rw [Walk.support_concat, List.mem_append, Walk.support_reverse,
        List.mem_reverse, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact Or.inl (hPint i y hy i' hi')
      · exact Or.inr rfl
  -- at least `k` fan paths
  have hrk : k ≤ r := by
    by_contra hlt
    push Not at hlt
    have hMr : M ≤ r := by
      rcases le_total k M with h | h
      · rw [min_eq_left h] at hr
        omega
      · rwa [min_eq_right h] at hr
    have hr0 : 0 < r := by omega
    obtain ⟨j, hj⟩ : ∃ j, t j % M = (t ⟨0, hr0⟩ + 1) % M := by
      have himg : Finset.univ.image (fun j => t j % M) = Finset.range M := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
          obtain ⟨j, rfl⟩ := hz
          exact Finset.mem_range.2 (Nat.mod_lt _ hf.pos)
        · rw [Finset.card_range, Finset.card_image_of_injective, Finset.card_univ,
            Fintype.card_fin]
          · exact hMr
          · intro i j h
            exact htinj i j (hf.eq_iff.2 h)
      have : (t ⟨0, hr0⟩ + 1) % M ∈ Finset.range M := Finset.mem_range.2 (Nat.mod_lt _ hf.pos)
      rw [← himg] at this
      simpa using this
    exact hnc ⟨0, hr0⟩ j (hf.eq_iff.2 hj)
  -- the set `{x} ∪ {successors}` is independent
  set S : Finset V := insert x (Finset.univ.image (fun j => f (t j + 1))) with hS
  have hScard : S.card = r + 1 := by
    rw [hS, Finset.card_insert_of_notMem, Finset.card_image_of_injective, Finset.card_univ,
      Fintype.card_fin]
    · intro i j h
      apply htinj i j
      rw [hf.eq_iff] at h ⊢
      exact Nat.ModEq.add_right_cancel' 1 h
    · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro j h
      exact hx _ h
  have hind : G.IsIndepSet (S : Set V) := by
    intro a ha b hb hab hadj
    simp only [hS, Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_insert_iff, Set.mem_range] at ha hb
    rcases ha with rfl | ⟨i, rfl⟩ <;> rcases hb with rfl | ⟨j, rfl⟩
    · exact hab rfl
    · exact hxs j hadj
    · exact hxs i hadj.symm
    · exact hcomb i j (fun h => hab (h ▸ rfl)) hadj
  have := hα _ hind
  rw [Set.ncard_coe_finset, hScard] at this
  omega

end Hamiltonicity
