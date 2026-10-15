/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MengerHamilton.CyclicArrangement

/-!
# Lengthening a cycle along a detour

If `C` is a cycle `f 0, f 1, …` and `Q` is a path of length at least two between two vertices
`f a`, `f b` of `C` whose interior avoids `C`, and `f (a + 1)` is adjacent to `f (b + 1)`, then
there is a cycle of length `|C| + |Q| - 1`.
-/

@[expose] public section

open SimpleGraph

namespace Hamiltonicity

variable {V : Type*}

namespace CycArr

variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}

/-- The detour construction with `a = 0` and `b = d`. -/
lemma extend_core (hC : CycArr G m f) {d : ℕ} (hd1 : 1 ≤ d) (hdm : d < m)
    (Q : G.Walk (f 0) (f d)) (hQ : Q.IsPath) (hQl : 2 ≤ Q.length)
    (hint : ∀ y ∈ Q.support, ∀ i, f i = y → y = f 0 ∨ y = f d)
    (hadj : G.Adj (f 1) (f (d + 1))) :
    ∃ g, CycArr G (m + Q.length - 1) g := by
  set l := Q.length with hl
  have hm := hC.three_le
  set q := Q.getVert with hq
  have hq0 : q 0 = f 0 := Q.getVert_zero
  have hql : q l = f d := Q.getVert_length
  have hqinj : ∀ i j, i ≤ l → j ≤ l → q i = q j → i = j := fun i j hi hj h =>
    hQ.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) h
  have hqoff : ∀ i, 0 < i → i < l → ∀ j, f j ≠ q i := by
    intro i hi0 hil j hj
    rcases hint (q i) (Q.getVert_mem_support i) j hj with h | h
    · have := hqinj i 0 (by omega) (by omega) (h.trans hq0.symm)
      omega
    · have := hqinj i l (by omega) le_rfl (h.trans hql.symm)
      omega
  have hfinj : ∀ i j, i < m → j < m → f i = f j → i = j := hC.inj
  set h : ℕ → V := fun j =>
    if j ≤ l then q j else if j < l + d then f (d + l - j) else f (j - l + 1) with hh
  have hA : ∀ j, j ≤ l → h j = q j := fun j hj => by
    simp only [hh]
    rw [ite_eq_left hj]
  have hB : ∀ j, l < j → j < l + d → h j = f (d + l - j) := fun j hj1 hj2 => by
    simp only [hh]
    rw [ite_eq_right (by omega), ite_eq_left hj2]
  have hC' : ∀ j, l + d ≤ j → h j = f (j - l + 1) := fun j hj => by
    simp only [hh]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  refine ⟨_, of_fun (h := h) (by omega) ?_ ?_ ?_⟩
  · -- injectivity
    have hcls : ∀ j, l < j → j < m + l - 1 → ∃ s, 0 < s ∧ s < m ∧ s ≠ d ∧ h j = f s ∧
        (j < l + d → s = d + l - j) ∧ (l + d ≤ j → s = j - l + 1) := by
      intro j hj1 hj2
      by_cases hjd : j < l + d
      · exact ⟨d + l - j, by omega, by omega, by omega, hB j hj1 hjd, fun _ => rfl,
          fun h' => by omega⟩
      · exact ⟨j - l + 1, by omega, by omega, by omega, hC' j (by omega), fun h' => by omega,
          fun _ => rfl⟩
    have hmix : ∀ a b, a ≤ l → l < b → b < m + l - 1 → h a ≠ h b := by
      intro a b ha hb1 hb2 hab
      obtain ⟨s, hs0, hsm, hsd, hs, -, -⟩ := hcls b hb1 hb2
      rw [hA a ha, hs] at hab
      by_cases ha0 : a = 0
      · subst ha0
        rw [hq0] at hab
        have := hfinj _ _ (by omega) hsm hab
        omega
      by_cases hal : a = l
      · subst hal
        rw [hql] at hab
        exact hsd (hfinj _ _ hsm (by omega) hab.symm)
      exact hqoff a (by omega) (by omega) s hab.symm
    intro a b ha hb hab
    by_cases ha' : a ≤ l <;> by_cases hb' : b ≤ l
    · rw [hA a ha', hA b hb'] at hab
      exact hqinj a b ha' hb' hab
    · exact absurd hab (hmix a b ha' (by omega) hb)
    · exact absurd hab.symm (hmix b a hb' (by omega) ha)
    · obtain ⟨s, hs0, hsm, hsd, hs, hs1, hs2⟩ := hcls a (by omega) ha
      obtain ⟨t, ht0, htm, htd, ht, ht1, ht2⟩ := hcls b (by omega) hb
      rw [hs, ht] at hab
      have hst := hfinj _ _ hsm htm hab
      by_cases h1 : a < l + d <;> by_cases h2 : b < l + d
      · have := hs1 h1
        have := ht1 h2
        omega
      · have := hs1 h1
        have := ht2 (by omega)
        omega
      · have := hs2 (by omega)
        have := ht1 h2
        omega
      · have := hs2 (by omega)
        have := ht2 (by omega)
        omega
  · -- adjacency
    intro j hj
    rcases lt_trichotomy j l with hjl | rfl | hjl
    · rw [hA j hjl.le, hA (j + 1) hjl]
      exact Q.adj_getVert_succ hjl
    · rw [hA _ le_rfl, hql]
      by_cases hd : d = 1
      · subst hd
        rw [hC' _ (by omega), show Q.length + 1 - Q.length + 1 = 1 + 1 by omega]
        exact hC.adj 1
      · rw [hB _ (by omega) (by omega), show d + Q.length - (Q.length + 1) = d - 1 by omega]
        have := hC.adj (d - 1)
        rw [show d - 1 + 1 = d by omega] at this
        exact this.symm
    · by_cases h1 : j + 1 < l + d
      · rw [hB j hjl (by omega), hB (j + 1) (by omega) h1]
        have := hC.adj (d + l - (j + 1))
        rw [show d + l - (j + 1) + 1 = d + l - j by omega] at this
        exact this.symm
      by_cases h2 : j + 1 = l + d
      · rw [hB j hjl (by omega), hC' (j + 1) (by omega), show d + l - j = 1 by omega,
          show j + 1 - l + 1 = d + 1 by omega]
        exact hadj
      · rw [hC' j (by omega), hC' (j + 1) (by omega), show j + 1 - l + 1 = j - l + 1 + 1 by omega]
        exact hC.adj _
  · -- closing up
    rw [hC' _ (by omega), hA 0 (Nat.zero_le _), hq0, show m + l - 1 - l + 1 = 0 + m by omega,
      hC.periodic]

/-- **Lengthening a cycle.** A path `Q` of length at least two between distinct vertices `f a`,
`f b` of a cycle, with interior off the cycle, together with an edge between the successors
`f (a + 1)` and `f (b + 1)`, gives a cycle of length `m + |Q| - 1`. -/
lemma extend (hC : CycArr G m f) {a b : ℕ} (hab : f a ≠ f b) (Q : G.Walk (f a) (f b))
    (hQ : Q.IsPath) (hQl : 2 ≤ Q.length)
    (hint : ∀ y ∈ Q.support, ∀ i, f i = y → y = f a ∨ y = f b)
    (hadj : G.Adj (f (a + 1)) (f (b + 1))) :
    ∃ g, CycArr G (m + Q.length - 1) g := by
  have hpos := hC.pos
  obtain ⟨d, hdm, hd⟩ : ∃ d, d < m ∧ (a + d) % m = b % m := by
    have ha := Nat.mod_add_div a m
    have ha' : a % m < m := Nat.mod_lt _ hpos
    have hb' : b % m < m := Nat.mod_lt _ hpos
    by_cases hle : a % m ≤ b % m
    · refine ⟨b % m - a % m, by omega, ?_⟩
      rw [show a + (b % m - a % m) = b % m + m * (a / m) by omega, Nat.add_mul_mod_self_left,
        Nat.mod_mod]
    · refine ⟨b % m + m - a % m, by omega, ?_⟩
      rw [show a + (b % m + m - a % m) = b % m + m * (a / m + 1) by rw [Nat.mul_succ]; omega,
        Nat.add_mul_mod_self_left, Nat.mod_mod]
  have hfb : f b = f (a + d) := (hC.eq_iff.2 hd).symm
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hab (by rw [hfb]; rfl)
  have hR := hC.rotate a
  have hQ' := hR.extend_core (d := d) (by omega) hdm (Q.copy rfl hfb)
    ((Walk.isPath_copy _ _ _).2 hQ) (by rwa [Walk.length_copy])
    (by
      intro y hy i hi
      rw [Walk.support_copy] at hy
      rcases hint y hy (a + i) hi with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans hfb))
    (by
      have := hC.eq_succ hfb
      rw [show a + (d + 1) = a + d + 1 by omega, ← this]
      exact hadj)
  rwa [Walk.length_copy] at hQ'

end CycArr

end Hamiltonicity
