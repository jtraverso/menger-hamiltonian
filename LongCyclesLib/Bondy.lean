/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LongCyclesLib.BondyA

/-!
# Bondy's theorem

Let `G` be Hamiltonian on `n ≥ 3` vertices with `n² ≤ 4 e(G)`. If `G` has no cycle of length
`n - 1`, the counting argument of `LongCyclesLib.BondyA` applies. Otherwise let `v` be the vertex missed
by a cycle of length `n - 1`: if `2 deg v ≥ n`, two neighbours of `v` at distance `ℓ - 2` along the
cycle close a cycle of length `ℓ`; if `2 deg v < n`, the graph `G - v` is Hamiltonian with
`(n - 1)² < 4 e(G - v)` and we conclude by induction (in the strict case `K_{n/2,n/2}` cannot
occur).
-/

@[expose] public section

open Finset SimpleGraph Hamiltonicity

namespace LongCycles

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If the vertex `v` missed by a cycle of length `n - 1` has degree at least `n / 2`, then `G`
has cycles of all lengths `3 ≤ ℓ ≤ n - 1`. -/
lemma caseB_high {g : ℕ → V} (hg : CycArr G (Fintype.card V - 1) g) {v : V}
    (hv : ∀ j, g j ≠ v) (hcov : ∀ w, w ≠ v → ∃ j, g j = w)
    (hd : Fintype.card V ≤ 2 * G.degree v) (ℓ : ℕ) (hℓ1 : 3 ≤ ℓ)
    (hℓ2 : ℓ ≤ Fintype.card V - 1) : ∃ f, CycArr G ℓ f := by
  set n := Fintype.card V with hn
  set m := n - 1 with hm
  have hm3 := hg.three_le
  have hcov' : ∀ w, G.Adj v w → ∃ j, g j = w := fun w hw => hcov w (G.ne_of_adj hw).symm
  have hA := degree_eq_count hg v hcov'
  have hB := degree_eq_count (hg.rotate (ℓ - 2)) v (fun w hw => by
    obtain ⟨j, rfl⟩ := hcov' w hw
    have : ℓ - 2 ≤ j + m * (ℓ - 2) := le_add_left (Nat.le_mul_of_pos_left _ (by omega))
    refine ⟨j + m * (ℓ - 2) - (ℓ - 2), ?_⟩
    rw [show ℓ - 2 + (j + m * (ℓ - 2) - (ℓ - 2)) = j + m * (ℓ - 2) by omega,
      cycArr_periodic_mul hg])
  set A := {p ∈ range m | G.Adj v (g p)} with hAdef
  set B := {p ∈ range m | G.Adj v (g (ℓ - 2 + p))} with hBdef
  have hU : #(A ∪ B) ≤ m := by
    calc #(A ∪ B) ≤ #(range m) := card_le_card (union_subset (filter_subset _ _)
          (filter_subset _ _))
      _ = m := card_range m
  have hI := card_union_add_card_inter A B
  obtain ⟨p, hp⟩ : (A ∩ B).Nonempty := card_pos.1 (by omega)
  rw [mem_inter, hAdef, hBdef, mem_filter, mem_filter, mem_range] at hp
  obtain ⟨⟨hpm, hpA⟩, -, hpB⟩ := hp
  have key : ∀ a b, p ≤ a → a < p + m → p ≤ b → b < p + m → g a = g b → a = b :=
    fun a b h1 h2 h3 h4 hab => mod_window' (hg.eq_iff.1 hab) h1 h2 h3 h4
  exact cycArr_of_window (G := G) (fun t => if t = 0 then v else g (p + t - 1)) (by omega)
    (fun s t hs ht hst => by
      by_cases hs0 : s = 0 <;> by_cases ht0 : t = 0
      · omega
      · rw [ite_eq_left hs0, ite_eq_right ht0] at hst
        exact absurd hst.symm (hv _)
      · rw [ite_eq_right hs0, ite_eq_left ht0] at hst
        exact absurd hst (hv _)
      · rw [ite_eq_right hs0, ite_eq_right ht0] at hst
        have := key _ _ (by omega) (by omega) (by omega) (by omega) hst
        omega)
    (fun t ht => by
      by_cases ht0 : t = 0
      · subst ht0
        rw [ite_eq_left rfl, ite_eq_right (by omega), show p + (0 + 1) - 1 = p by omega]
        exact hpA
      · rw [ite_eq_right ht0, ite_eq_right (by omega)]
        have := hg.adj (p + t - 1)
        rwa [show p + t - 1 + 1 = p + (t + 1) - 1 by omega] at this)
    (by
      rw [ite_eq_right (by omega), ite_eq_left rfl, show p + (ℓ - 1) - 1 = ℓ - 2 + p by omega]
      exact hpB.symm)

/-- The reduction step: if `G` has a cycle of length `n - 1` and the strict version of the theorem
holds on `n - 1` vertices, then `G` is pancyclic. -/
lemma pancyc_of_pred {f : ℕ → V} (hf : CycArr G (Fintype.card V) f) (h4 : 4 ≤ Fintype.card V)
    {g : ℕ → V} (hg : CycArr G (Fintype.card V - 1) g)
    (hE : Fintype.card V ^ 2 ≤ 4 * #G.edgeFinset)
    (ih : ∀ {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W = Fintype.card V - 1 → (∃ f, CycArr H (Fintype.card V - 1) f) →
      (Fintype.card V - 1) ^ 2 < 4 * #H.edgeFinset →
      ∀ ℓ, 3 ≤ ℓ → ℓ ≤ Fintype.card V - 1 → ∃ f, CycArr H ℓ f)
    (ℓ : ℕ) (hℓ1 : 3 ≤ ℓ) (hℓ2 : ℓ ≤ Fintype.card V) : ∃ f, CycArr G ℓ f := by
  classical
  set n := Fintype.card V with hn
  by_cases hℓn : ℓ = n
  · exact ⟨f, hℓn ▸ hf⟩
  obtain ⟨v, hv, hcov⟩ := cycArr_exists_missing hg
  by_cases hd : n ≤ 2 * G.degree v
  · exact caseB_high hg hv hcov hd ℓ hℓ1 (by omega)
  have hS : ∀ j, g j ∈ univ.erase v := fun j => mem_erase.2 ⟨hv j, mem_univ _⟩
  have hdel := del_edges (G := G) v
  have hsq : (n - 1) ^ 2 + 2 * (n - 1) + 1 = n ^ 2 := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    ring
  obtain ⟨f', hf'⟩ := ih (indS G (univ.erase v)) (card_del v) ⟨_, cycArr_del hg hS⟩
    (by omega) ℓ hℓ1 (by omega)
  exact ⟨_, cycArr_undel hf'⟩

/-- **Bondy's theorem, strict version**: a Hamiltonian graph on `n ≥ 3` vertices with more than
`n² / 4` edges is pancyclic. -/
theorem bondy_strict : ∀ (n : ℕ) {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Fintype.card V = n → (∃ f, CycArr G n f) →
    n ^ 2 < 4 * #G.edgeFinset → ∀ ℓ, 3 ≤ ℓ → ℓ ≤ n → ∃ f, CycArr G ℓ f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ G _ hcard ⟨f, hf⟩ hE ℓ hℓ1 hℓ2
  subst hcard
  have h3 := hf.three_le
  by_cases hℓn : ℓ = Fintype.card V
  · exact ⟨f, hℓn ▸ hf⟩
  have h4 : 4 ≤ Fintype.card V := by omega
  by_cases hno : ∀ g, ¬ CycArr G (Fintype.card V - 1) g
  · have := (caseA hf h4 hno).1
    omega
  push Not at hno
  obtain ⟨g, hg⟩ := hno
  exact pancyc_of_pred hf h4 hg hE.le (fun H _ hc hH hE' => ih _ (by omega) H hc hH hE') ℓ hℓ1
    hℓ2

/-- **Bondy's theorem** in terms of cyclic arrangements. -/
theorem bondy_cycArr {f : ℕ → V} (hf : CycArr G (Fintype.card V) f)
    (hE : Fintype.card V ^ 2 ≤ 4 * #G.edgeFinset) :
    (∀ ℓ, 3 ≤ ℓ → ℓ ≤ Fintype.card V → ∃ f, CycArr G ℓ f) ∨
      (Even (Fintype.card V) ∧
        Nonempty (G ≃g completeBipartiteGraph (Fin (Fintype.card V / 2))
          (Fin (Fintype.card V / 2)))) := by
  set n := Fintype.card V with hn
  have h3 := hf.three_le
  by_cases hlt : n ^ 2 < 4 * #G.edgeFinset
  · exact Or.inl (bondy_strict n G rfl ⟨f, hf⟩ hlt)
  by_cases h3' : n = 3
  · refine Or.inl fun ℓ hℓ1 hℓ2 => ⟨f, ?_⟩
    rwa [show ℓ = n by omega]
  have h4 : 4 ≤ n := by omega
  by_cases hno : ∀ g, ¬ CycArr G (n - 1) g
  · exact Or.inr ((caseA hf h4 hno).2 hE)
  push Not at hno
  obtain ⟨g, hg⟩ := hno
  exact Or.inl (pancyc_of_pred hf h4 hg hE
    (fun H _ hc hH hE' => bondy_strict _ H hc hH hE'))

end LongCycles
