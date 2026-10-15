/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MengerHamilton.CyclicArrangement

/-!
# The Bondy–Chvátal closure step

A Hamiltonian path whose end vertices have degree sum at least `n` closes up to a Hamiltonian
cycle; consequently adding an edge between two non-adjacent vertices with degree sum at least
`n` does not create Hamiltonicity.
-/

@[expose] public section

open SimpleGraph

namespace Hamiltonicity

variable {V : Type*}

/-- A Hamiltonian path `x 0, …, x (n - 1)` whose ends have degree sum at least `n` can be closed
into a Hamiltonian cycle. -/
lemma exists_cycArr_of_path [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : ℕ → V) (hn : 3 ≤ Fintype.card V)
    (hinj : ∀ i j, i < Fintype.card V → j < Fintype.card V → x i = x j → i = j)
    (hadj : ∀ i, i + 1 < Fintype.card V → G.Adj (x i) (x (i + 1)))
    (hdeg : Fintype.card V ≤ G.degree (x 0) + G.degree (x (Fintype.card V - 1))) :
    ∃ g, CycArr G (Fintype.card V) g := by
  classical
  set n := Fintype.card V with hn_def
  have hsurj : ∀ w, ∃ j < n, x j = w := by
    have himg : (Finset.range n).image x = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      exact hinj i j (by simpa using hi) (by simpa using hj) hij
    intro w
    have : w ∈ (Finset.range n).image x := himg ▸ Finset.mem_univ w
    simpa using this
  set I := (Finset.range (n - 1)).filter (fun i => G.Adj (x 0) (x (i + 1))) with hI_def
  set J := (Finset.range (n - 1)).filter (fun i => G.Adj (x (n - 1)) (x i)) with hJ_def
  have hI : I.card = G.degree (x 0) := by
    rw [← card_neighborFinset_eq_degree]
    have : G.neighborFinset (x 0) = I.image (fun i => x (i + 1)) := by
      ext w
      simp only [mem_neighborFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_range, I]
      constructor
      · intro hw
        obtain ⟨j, hj, rfl⟩ := hsurj w
        have hj0 : j ≠ 0 := by rintro rfl; exact G.irrefl hw
        refine ⟨j - 1, ⟨by omega, ?_⟩, ?_⟩
        · rwa [Nat.sub_add_cancel (by omega)]
        · rw [Nat.sub_add_cancel (by omega)]
      · rintro ⟨i, ⟨_, hi⟩, rfl⟩
        exact hi
    rw [this, Finset.card_image_of_injOn]
    intro i hi j hj hij
    have hi' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1
    have hj' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1
    have := hinj _ _ (by omega) (by omega) hij
    omega
  have hJ : J.card = G.degree (x (n - 1)) := by
    rw [← card_neighborFinset_eq_degree]
    have : G.neighborFinset (x (n - 1)) = J.image x := by
      ext w
      simp only [mem_neighborFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_range, J]
      constructor
      · intro hw
        obtain ⟨j, hj, rfl⟩ := hsurj w
        have hj0 : j ≠ n - 1 := by rintro rfl; exact G.irrefl hw
        exact ⟨j, ⟨by omega, hw⟩, rfl⟩
      · rintro ⟨i, ⟨_, hi⟩, rfl⟩
        exact hi
    rw [this, Finset.card_image_of_injOn]
    intro i hi j hj hij
    have hi' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1
    have hj' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1
    exact hinj _ _ (by omega) (by omega) hij
  have hex : ∃ i, i < n - 1 ∧ G.Adj (x 0) (x (i + 1)) ∧ G.Adj (x (n - 1)) (x i) := by
    by_contra hne
    push Not at hne
    have hdisj : Disjoint I J := by
      rw [Finset.disjoint_left]
      intro i hiI hiJ
      simp only [I, J, Finset.mem_filter, Finset.mem_range] at hiI hiJ
      exact hne i hiI.1 hiI.2 hiJ.2
    have h1 := Finset.card_union_of_disjoint hdisj
    have hsub : I ∪ J ⊆ Finset.range (n - 1) :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_range] at h2
    omega
  obtain ⟨i, hi, hu, hv⟩ := hex
  let h : ℕ → V := fun j => if j ≤ i then x j else if j < n then x (n + i - j) else x 0
  refine ⟨_, CycArr.of_fun (h := h) hn ?_ ?_ ?_⟩
  · intro a b ha hb hab
    have key : ∀ j, j < n → h j = x (if j ≤ i then j else n + i - j) := by
      intro j hj
      simp only [h]
      split_ifs <;> rfl
    rw [key a ha, key b hb] at hab
    have := hinj _ _ (by split_ifs <;> omega) (by split_ifs <;> omega) hab
    split_ifs at this <;> omega
  · intro j hj
    rcases lt_trichotomy j i with hji | rfl | hji
    · have e1 : h j = x j := ite_eq_left hji.le
      have e2 : h (j + 1) = x (j + 1) := ite_eq_left hji
      rw [e1, e2]
      exact hadj j (by omega)
    · have e1 : h j = x j := ite_eq_left le_rfl
      have e2 : h (j + 1) = x (n - 1) := by
        simp only [h]
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        congr 1; omega
      rw [e1, e2]
      exact hv.symm
    · by_cases hjn : j + 1 < n
      · have e1 : h j = x (n + i - j) := by
          simp only [h]
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        have e2 : h (j + 1) = x (n + i - j - 1) := by
          simp only [h]
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
          congr 1
        rw [e1, e2]
        have := hadj (n + i - j - 1) (by omega)
        rw [show n + i - j - 1 + 1 = n + i - j by omega] at this
        exact this.symm
      · have e1 : h j = x (i + 1) := by
          simp only [h]
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
          congr 1; omega
        have e2 : h (j + 1) = x 0 := by
          simp only [h]
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        rw [e1, e2]
        exact hu.symm
  · simp only [h]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (Nat.zero_le _)]

/-- The forward direction of the Bondy–Chvátal closure step. -/
lemma isHamiltonian_of_sup_edge [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v)
    (hH : (G ⊔ edge u v).IsHamiltonian) : G.IsHamiltonian := by
  set n := Fintype.card V with hn_def
  have hdu : G.degree u + 2 ≤ n := by
    rw [← card_neighborFinset_eq_degree]
    have h1 : u ∉ insert v (G.neighborFinset u) := by simp [huv]
    have h2 : v ∉ G.neighborFinset u := by simpa using hnadj
    have := Finset.card_le_univ (insert u (insert v (G.neighborFinset u)))
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2] at this
    omega
  have hdv : G.degree v + 2 ≤ n := by
    rw [← card_neighborFinset_eq_degree]
    have h1 : v ∉ insert u (G.neighborFinset v) := by simp [huv.symm]
    have h2 : u ∉ G.neighborFinset v := by simpa [G.adj_comm] using hnadj
    have := Finset.card_le_univ (insert v (insert u (G.neighborFinset v)))
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2] at this
    omega
  have hn : 3 ≤ n := by omega
  obtain ⟨f, hf⟩ := exists_cycArr_of_isHamiltonian hH hn
  by_cases hall : ∀ i, G.Adj (f i) (f (i + 1))
  · exact CycArr.isHamiltonian ⟨hf.three_le, hf.periodic, hf.inj, hall⟩ rfl
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  have huvi : (f i = u ∧ f (i + 1) = v) ∨ (f i = v ∧ f (i + 1) = u) := by
    have := hf.adj i
    rw [sup_adj] at this
    rcases this with h | h
    · exact absurd h hi
    · rw [edge_adj] at h
      exact h.1
  have hrot := hf.rotate (i + 1)
  set x : ℕ → V := fun j => f (i + 1 + j) with hx
  have hx0 : x 0 = f (i + 1) := rfl
  have hxn : x (n - 1) = f i := by
    simp only [x]
    rw [show i + 1 + (n - 1) = i + n by omega, hf.periodic]
  have hadj : ∀ j, j + 1 < n → G.Adj (x j) (x (j + 1)) := by
    intro j hj
    by_contra hne
    have := hrot.adj j
    rw [sup_adj] at this
    rcases this with h | h
    · exact hne h
    rw [edge_adj] at h
    have hcases : (x j = x (n - 1) ∧ x (j + 1) = x 0) ∨ (x j = x 0 ∧ x (j + 1) = x (n - 1)) := by
      rw [hx0, hxn]
      rcases huvi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h.1 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        simp [h1, h2, h3, h4]
    rcases hcases with ⟨h1, -⟩ | ⟨h1, h2⟩
    · have := hrot.inj _ _ (by omega) (by omega) h1
      omega
    · have := hrot.inj _ _ (by omega) (by omega) h1
      subst this
      have := hrot.inj _ _ (by omega) (by omega) h2
      omega
  rcases huvi with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- the path runs from `v` to `u`
    obtain ⟨g, hg⟩ := exists_cycArr_of_path G x hn hrot.inj hadj
      (by rw [hx0, hxn, h1, h2]; omega)
    exact hg.isHamiltonian rfl
  · -- reverse the path
    let y : ℕ → V := fun j => x (n - 1 - j)
    obtain ⟨g, hg⟩ := exists_cycArr_of_path G y hn
      (by
        intro a b ha hb hab
        have := hrot.inj _ _ (by omega) (by omega) hab
        omega)
      (by
        intro j hj
        have := hadj (n - 1 - (j + 1)) (by omega)
        rw [show n - 1 - (j + 1) + 1 = n - 1 - j by omega] at this
        exact this.symm)
      (by
        have hy0 : y 0 = v := by simp only [y, Nat.sub_zero]; rw [hxn, h1]
        have hyn : y (Fintype.card V - 1) = u := by
          simp only [y]
          rw [show n - 1 - (Fintype.card V - 1) = 0 by omega, hx0, h2]
        rw [add_comm] at hdeg
        convert hdeg using 3)
    exact hg.isHamiltonian rfl

end Hamiltonicity
