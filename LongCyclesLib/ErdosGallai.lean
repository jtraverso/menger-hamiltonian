/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LongCyclesLib.Dirac

/-!
# The Erdős–Gallai theorem on cycles: the induction

For a graph `G` without cycles of length at least `k` we show, by strong induction on `|S|`, that
for every vertex set `S` the degrees inside `S` sum to at most `(k - 1)(|S| - 1)`. Vertices of
small degree are deleted, separations of order at most one are split, and in the remaining
(2-connected) case Dirac's long cycle lemma gives a contradiction.
-/

@[expose] public section

open Finset SimpleGraph

namespace LongCycles

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of neighbours of `v` in `S`. -/
def dS (S : Finset V) (v : V) : ℕ := #{u ∈ S | G.Adj v u}

omit [DecidableEq V] in
lemma dS_le (S : Finset V) {v : V} (hv : v ∈ S) : dS G S v ≤ #S - 1 := by
  classical
  have : {u ∈ S | G.Adj v u} ⊆ S.erase v := by
    intro u hu
    rw [mem_filter] at hu
    exact mem_erase.2 ⟨fun h => G.irrefl (h ▸ hu.2), hu.1⟩
  have := card_le_card this
  rw [card_erase_of_mem hv] at this
  exact this

lemma sum_dS_erase (S : Finset V) {v : V} (hv : v ∈ S) :
    ∑ u ∈ S, dS G S u = ∑ u ∈ S.erase v, dS G (S.erase v) u + 2 * dS G S v := by
  have h1 : ∀ u, dS G S u = dS G (S.erase v) u + if G.Adj u v then 1 else 0 := by
    intro u
    unfold dS
    rw [filter_erase]
    split_ifs with h
    · rw [card_erase_of_mem (by simp [hv, h])]
      have : 0 < #{w ∈ S | G.Adj u w} := card_pos.2 ⟨v, by simp [hv, h]⟩
      omega
    · rw [erase_eq_of_notMem (by simp [h])]; rfl
  have h2 : ∑ u ∈ S.erase v, (if G.Adj u v then 1 else 0) = dS G S v := by
    rw [sum_boole, Nat.cast_id, dS]
    congr 1
    ext u
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨-, hu⟩, h⟩; exact ⟨hu, h.symm⟩
    · rintro ⟨hu, h⟩; exact ⟨⟨fun h' => G.irrefl (h' ▸ h), hu⟩, h.symm⟩
  rw [← add_sum_erase S _ hv]
  simp_rw [h1 _]
  rw [sum_add_distrib, h2]
  have : dS G S v = dS G (S.erase v) v + if G.Adj v v then 1 else 0 := h1 v
  simp only [SimpleGraph.irrefl, ite_false, add_zero] at this
  simp only [SimpleGraph.irrefl, ite_false, add_zero]
  rw [← this]
  ring

lemma sum_dS_split (S S1 S2 : Finset V) (hS : S1 ∪ S2 = S)
    (hno : ∀ u ∈ S1, u ∉ S2 → ∀ w ∈ S2, w ∉ S1 → ¬ G.Adj u w) :
    ∑ u ∈ S, dS G S u ≤ ∑ u ∈ S1, dS G S1 u + ∑ u ∈ S2, dS G S2 u := by
  have h1 : S1 ⊆ S := hS ▸ subset_union_left
  have h2 : S2 ⊆ S := hS ▸ subset_union_right
  have hpt : ∀ u ∈ S, dS G S u ≤ (if u ∈ S1 then dS G S1 u else 0) +
      (if u ∈ S2 then dS G S2 u else 0) := by
    intro u hu
    unfold dS
    by_cases hu1 : u ∈ S1 <;> by_cases hu2 : u ∈ S2 <;> simp only [hu1, hu2, ite_true, ite_false,
      add_zero, zero_add]
    · calc #{w ∈ S | G.Adj u w} ≤ #({w ∈ S1 | G.Adj u w} ∪ {w ∈ S2 | G.Adj u w}) := by
            apply card_le_card
            intro w hw
            rw [mem_filter, ← hS, mem_union] at hw
            rw [mem_union, mem_filter, mem_filter]
            tauto
        _ ≤ _ := card_union_le _ _
    · apply card_le_card
      intro w hw
      rw [mem_filter, ← hS, mem_union] at hw
      rw [mem_filter]
      rcases hw with ⟨hw | hw, hadj⟩
      · exact ⟨hw, hadj⟩
      · by_cases hw1 : w ∈ S1
        · exact ⟨hw1, hadj⟩
        · exact absurd hadj (hno u hu1 hu2 w hw hw1)
    · apply card_le_card
      intro w hw
      rw [mem_filter, ← hS, mem_union] at hw
      rw [mem_filter]
      rcases hw with ⟨hw | hw, hadj⟩
      · by_cases hw2 : w ∈ S2
        · exact ⟨hw2, hadj⟩
        · exact absurd hadj.symm (hno w hw hw2 u hu2 hu1)
      · exact ⟨hw, hadj⟩
    · exfalso
      rw [← hS, mem_union] at hu
      tauto
  calc ∑ u ∈ S, dS G S u
      ≤ ∑ u ∈ S, ((if u ∈ S1 then dS G S1 u else 0) + (if u ∈ S2 then dS G S2 u else 0)) :=
        sum_le_sum hpt
    _ = ∑ u ∈ S1, dS G S1 u + ∑ u ∈ S2, dS G S2 u := by
        rw [sum_add_distrib, sum_ite_mem, sum_ite_mem, inter_eq_right.2 h1,
          inter_eq_right.2 h2]

/-- The graph induced on a finite vertex set `S`, as a graph on the subtype. -/
abbrev indS (S : Finset V) : SimpleGraph S := G.comap (fun x : S => x.1)

omit [DecidableEq V] in
lemma degree_indS (S : Finset V) [DecidableRel (indS G S).Adj] (v : S) :
    (indS G S).degree v = dS G S v := by
  rw [← card_neighborFinset_eq_degree, dS]
  refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha
    rw [mem_neighborFinset, comap_adj] at ha
    exact mem_filter.2 ⟨a.2, ha⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro b hb
    rw [mem_filter] at hb
    exact ⟨⟨b, hb.1⟩, by rw [mem_neighborFinset, comap_adj]; exact hb.2, rfl⟩

omit [DecidableRel G.Adj] in
/-- The no-separation hypothesis gives the connectivity hypothesis of Dirac's lemma. -/
lemma conn_of_noSep (S : Finset V)
    (hsep : ∀ S1 S2 : Finset V, S1 ∪ S2 = S → #(S1 ∩ S2) ≤ 1 → #S1 < #S → #S2 < #S →
      ∃ u ∈ S1, u ∉ S2 ∧ ∃ w ∈ S2, w ∉ S1 ∧ G.Adj u w)
    (w y z : S) (hy : y ≠ w) (hz : z ≠ w) :
    ∃ p : (indS G S).Walk y z, w ∉ p.support := by
  classical
  by_contra hno
  push Not at hno
  set R : Finset V := {x ∈ S | ∃ hx : x ∈ S, ∃ p : (indS G S).Walk y ⟨x, hx⟩, w ∉ p.support}
    with hR
  have hRS : R ⊆ S := filter_subset _ _
  have hwR : w.1 ∉ R := by
    intro h
    rw [hR, mem_filter] at h
    obtain ⟨-, hx, p, hp⟩ := h
    exact hp (by simp)
  have hyR : y.1 ∈ R := by
    rw [hR, mem_filter]
    exact ⟨y.2, y.2, Walk.nil, by simpa using hy.symm⟩
  have hzR : z.1 ∉ R := by
    intro h
    rw [hR, mem_filter] at h
    obtain ⟨-, hx, p, hp⟩ := h
    exact hp (hno p)
  obtain ⟨u, hu1, hu2, x, hx2, hx1, hux⟩ := hsep (insert w.1 R) (S \ R)
    (by
      ext a
      simp only [mem_union, mem_insert, mem_sdiff]
      constructor
      · rintro ((h | h) | h)
        · exact h ▸ w.2
        · exact hRS h
        · exact h.1
      · intro h
        by_cases ha : a ∈ R
        · exact Or.inl (Or.inr ha)
        · exact Or.inr ⟨h, ha⟩)
    (by
      calc #(insert w.1 R ∩ (S \ R)) ≤ #({w.1} : Finset V) := by
            apply card_le_card
            intro a ha
            simp only [mem_inter, mem_insert, mem_sdiff] at ha
            rcases ha with ⟨h | h, -, h'⟩
            · exact mem_singleton.2 h
            · exact absurd h h'
        _ = 1 := card_singleton _)
    (by
      apply card_lt_card
      refine ⟨?_, fun h => ?_⟩
      · intro a ha
        rcases mem_insert.1 ha with h | h
        · exact h ▸ w.2
        · exact hRS h
      · rcases mem_insert.1 (h z.2) with h' | h'
        · exact hz (Subtype.ext h')
        · exact hzR h')
    (by
      apply card_lt_card
      refine ⟨sdiff_subset, fun h => ?_⟩
      exact (mem_sdiff.1 (h y.2)).2 hyR)
  have huR : u ∈ R := by
    rcases mem_insert.1 hu1 with h | h
    · exact absurd (mem_sdiff.2 ⟨h ▸ w.2, h ▸ hwR⟩) hu2
    · exact h
  have hxw : x ≠ w.1 := fun h => hx1 (mem_insert.2 (Or.inl h))
  have hxR : x ∉ R := fun h => hx1 (mem_insert.2 (Or.inr h))
  have hxS : x ∈ S := (mem_sdiff.1 hx2).1
  apply hxR
  rw [hR, mem_filter] at huR ⊢
  obtain ⟨-, hu, p, hp⟩ := huR
  have hadj : (indS G S).Adj ⟨u, hu⟩ ⟨x, hxS⟩ := by rw [comap_adj]; exact hux
  refine ⟨hxS, hxS, p.concat hadj, ?_⟩
  rw [Walk.support_concat, List.mem_append, List.mem_singleton, not_or]
  exact ⟨hp, fun h => hxw (congrArg Subtype.val h).symm⟩

/-- In the 2-connected case Dirac's lemma provides a long cycle. -/
lemma long_cycle_of_noSep (S : Finset V) {k : ℕ} (hk : 3 ≤ k) (hn : k ≤ #S)
    (hdeg : ∀ v ∈ S, k ≤ 2 * dS G S v)
    (hsep : ∀ S1 S2 : Finset V, S1 ∪ S2 = S → #(S1 ∩ S2) ≤ 1 → #S1 < #S → #S2 < #S →
      ∃ u ∈ S1, u ∉ S2 ∧ ∃ w ∈ S2, w ∉ S1 ∧ G.Adj u w) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length := by
  classical
  obtain ⟨u, c, hc, hlen⟩ := dirac_long_cycle (indS G S) hk (by rw [Fintype.card_coe]; exact hn)
    (fun v => by rw [degree_indS]; exact hdeg v v.2) (conn_of_noSep G S hsep)
  let f : indS G S →g G := ⟨fun x => x.1, fun h => h⟩
  refine ⟨u.1, c.map f, ?_, ?_⟩
  · exact (Walk.isCycle_map_iff_of_injective Subtype.val_injective).2 hc
  · rw [Walk.length_map]; exact hlen

omit [DecidableEq V] in
/-- **The Erdős–Gallai induction.** -/
theorem sum_dS_le {k : ℕ} (hk : 3 ≤ k)
    (h : ∀ (u : V) (c : G.Walk u u), c.IsCycle → c.length < k) (S : Finset V) :
    ∑ v ∈ S, dS G S v ≤ (k - 1) * (#S - 1) := by
  classical
  induction hS : #S using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  by_cases h1 : n < k
  · calc ∑ v ∈ S, dS G S v ≤ #S • (#S - 1) := sum_le_card_nsmul _ _ _ (fun v hv => dS_le G S hv)
      _ = n * (n - 1) := by rw [hS, smul_eq_mul]
      _ ≤ (k - 1) * (n - 1) := Nat.mul_le_mul_right _ (by omega)
  by_cases h2 : ∃ v ∈ S, 2 * dS G S v ≤ k - 1
  · obtain ⟨v, hv, hdv⟩ := h2
    have hcard : #(S.erase v) = n - 1 := by rw [card_erase_of_mem hv, hS]
    have := ih (n - 1) (by omega) (S.erase v) hcard
    rw [sum_dS_erase G S hv]
    calc _ ≤ (k - 1) * (n - 1 - 1) + (k - 1) := by omega
      _ = (k - 1) * (n - 1) := by
        rw [← Nat.mul_succ]; congr 1; omega
  by_cases h3 : ∃ S1 S2 : Finset V, S1 ∪ S2 = S ∧ #(S1 ∩ S2) ≤ 1 ∧ #S1 < #S ∧ #S2 < #S ∧
      ∀ u ∈ S1, u ∉ S2 → ∀ w ∈ S2, w ∉ S1 → ¬ G.Adj u w
  · obtain ⟨S1, S2, hU, hI, hlt1, hlt2, hno⟩ := h3
    have e1 := ih #S1 (by omega) S1 rfl
    have e2 := ih #S2 (by omega) S2 rfl
    have hc := card_union_add_card_inter S1 S2
    rw [hU] at hc
    calc _ ≤ _ := sum_dS_split G S S1 S2 hU hno
      _ ≤ (k - 1) * (#S1 - 1) + (k - 1) * (#S2 - 1) := Nat.add_le_add e1 e2
      _ = (k - 1) * (#S1 - 1 + (#S2 - 1)) := (Nat.mul_add _ _ _).symm
      _ ≤ (k - 1) * (n - 1) := Nat.mul_le_mul_left _ (by omega)
  exfalso
  push Not at h2 h3
  obtain ⟨u, c, hc, hlen⟩ := long_cycle_of_noSep G S hk (by omega) (fun v hv => by
    have := h2 v hv; omega) (fun S1 S2 hU hI hlt1 hlt2 => by
      obtain ⟨u, hu1, hu2, w, hw2, hw1, huw⟩ := h3 S1 S2 hU hI hlt1 hlt2
      exact ⟨u, hu1, hu2, w, hw2, hw1, huw⟩)
  exact absurd (h u c hc) (by omega)

omit [DecidableEq V] in
lemma dS_univ [Fintype V] (v : V) : dS G univ v = G.degree v := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  rfl

omit [DecidableEq V] in
theorem eg_cycle_aux [Fintype V] {k : ℕ} (hk : 3 ≤ k)
    (h : ∀ (u : V) (c : G.Walk u u), c.IsCycle → c.length < k) :
    2 * #G.edgeFinset ≤ (k - 1) * (Fintype.card V - 1) := by
  classical
  have := sum_dS_le G hk h univ
  simp only [dS_univ, card_univ] at this
  rw [← sum_degrees_eq_twice_card_edges]
  exact this

lemma mod_window {L s t : ℕ} (h : s % L = t % L) (hst : s ≤ t) (hlt : t < s + L) : s = t := by
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  rw [Nat.mod_eq_of_lt (by omega)] at h1
  omega

/-- The graph `G` together with an apex vertex `none` adjacent to every vertex of `G`. -/
def apex (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | some u, some v => G.Adj u v
    | none, some _ => True
    | some _, none => True
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by intro a h; cases a <;> simp_all⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma apex_some_some (u v : V) : (apex G).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma apex_none_some (v : V) : (apex G).Adj none (some v) := trivial

omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma apex_some_none (v : V) : (apex G).Adj (some v) none := trivial

omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma apex_none_none : ¬ (apex G).Adj none none := fun h => h

omit [DecidableEq V] in
lemma apex_edges [Fintype V] [DecidableRel (apex G).Adj] :
    #(apex G).edgeFinset = #G.edgeFinset + Fintype.card V := by
  classical
  have h1 := sum_degrees_eq_twice_card_edges (apex G)
  have h2 := sum_degrees_eq_twice_card_edges G
  have hd : ∀ x, (apex G).degree x = ∑ y, if (apex G).Adj x y then 1 else 0 := by
    intro x
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]
  have hd' : ∀ x, G.degree x = ∑ y, if G.Adj x y then 1 else 0 := by
    intro x
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]
  simp only [hd, Fintype.sum_option, apex_none_none, apex_none_some, apex_some_none,
    apex_some_some, ite_true, ite_false, sum_const, card_univ, smul_eq_mul, mul_one,
    zero_add] at h1
  simp only [hd'] at h2
  rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one, h2] at h1
  convert (show #(apex G).edgeFinset = #G.edgeFinset + Fintype.card V by omega)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A cycle of length `L` in the apex graph yields a path of length `L - 2` in `G`. -/
lemma path_of_apex_cycle {L : ℕ} {f : ℕ → Option V} (hf : Hamiltonicity.CycArr (apex G) L f) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length + 2 = L := by
  classical
  have hL := hf.three_le
  obtain ⟨j, hj⟩ : ∃ j, ∀ t, j < t → t < j + L → f t ≠ none := by
    by_cases hn : ∃ j < L, f j = none
    · obtain ⟨j, -, hj⟩ := hn
      refine ⟨j, fun t ht1 ht2 ht => ?_⟩
      rw [← hj, hf.eq_iff] at ht
      have := mod_window ht.symm (by omega) (by omega)
      omega
    · push Not at hn
      refine ⟨0, fun t _ _ ht => hn (t % L) (Nat.mod_lt _ (by omega)) ?_⟩
      rw [← hf.eq_mod]; exact ht
  obtain ⟨d, -⟩ : ∃ d : V, f (j + 1) = some d := Option.ne_none_iff_exists'.1 (hj _ (by omega)
    (by omega))
  set x : ℕ → V := fun t => (f t).getD d with hx
  have hfx : ∀ t, j < t → t < j + L → f t = some (x t) := by
    intro t h1 h2
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (hj t h1 h2)
    simp [hx, ha]
  obtain ⟨p, hp, hlen⟩ := exists_path_of_list (G := G) (seg x (j + 1) (L - 1))
    (isChain_seg _ _ _ (fun t h1 h2 => by
      have := hf.adj t
      rw [hfx t (by omega) (by omega), hfx (t + 1) (by omega) (by omega)] at this
      exact this))
    (nodup_seg _ _ _ (fun s t h1 h2 h3 h4 hst => by
      have := hfx s (by omega) (by omega)
      rw [hst, ← hfx t (by omega) (by omega), hf.eq_iff] at this
      rcases le_total s t with hst' | hst'
      · exact mod_window this hst' (by omega)
      · exact (mod_window this.symm hst' (by omega)).symm))
    (head?_seg _ _ _ (by omega)) (getLast?_seg _ _ _ (by omega))
  refine ⟨_, _, p, hp, ?_⟩
  rw [length_seg] at hlen
  omega

omit [DecidableEq V] in
theorem eg_path_aux [Fintype V] {k : ℕ}
    (h : ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length + 2 ≤ k) :
    2 * #G.edgeFinset ≤ (k - 2) * Fintype.card V := by
  classical
  by_cases hV : IsEmpty V
  · simp only [Fintype.card_eq_zero, mul_zero, nonpos_iff_eq_zero, mul_eq_zero,
      OfNat.ofNat_ne_zero, false_or, card_eq_zero, edgeFinset_eq_empty]
    ext a
    exact isEmptyElim a
  rw [not_isEmpty_iff] at hV
  obtain ⟨v⟩ := hV
  have hk : 2 ≤ k := by simpa using h v v Walk.nil Walk.IsPath.nil
  have hc := eg_cycle_aux (apex G) (k := k + 1) (by omega) (fun u c hc => by
    by_contra hlt
    obtain ⟨a, b, p, hp, hlen⟩ := path_of_apex_cycle G (Hamiltonicity.cycArr_of_isCycle hc)
    have := h a b p hp
    omega)
  rw [apex_edges, Fintype.card_option] at hc
  simp only [Nat.add_sub_cancel] at hc
  have : k * Fintype.card V = (k - 2) * Fintype.card V + 2 * Fintype.card V := by
    rw [← Nat.add_mul]; congr 1; omega
  omega

end LongCycles
