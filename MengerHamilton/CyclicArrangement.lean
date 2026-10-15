/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MengerHamilton.Menger

/-!
# Cyclic arrangements

Auxiliary material for the Hamiltonicity results: a cycle of length `m` in a graph `G` is
represented by a periodic function `f : ℕ → V` of period `m`, injective on `[0, m)`, with
consecutive values adjacent (`CycArr`). We relate this to Mathlib's cycles and Hamiltonian
cycles.
-/

@[expose] public section

open SimpleGraph

namespace Hamiltonicity

variable {V : Type*}

/-- A cyclic arrangement of length `m` in `G`: a periodic function of period `m`, injective on
`[0, m)`, whose consecutive values are adjacent. -/
structure CycArr (G : SimpleGraph V) (m : ℕ) (f : ℕ → V) : Prop where
  three_le : 3 ≤ m
  periodic : ∀ i, f (i + m) = f i
  inj : ∀ i j, i < m → j < m → f i = f j → i = j
  adj : ∀ i, G.Adj (f i) (f (i + 1))

namespace CycArr

variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}

lemma pos (h : CycArr G m f) : 0 < m := by have := h.three_le; omega

lemma eq_mod (h : CycArr G m f) (i : ℕ) : f i = f (i % m) := by
  conv_lhs => rw [← Nat.mod_add_div i m]
  induction i / m with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, h.periodic, ih]

lemma eq_iff (h : CycArr G m f) {i j : ℕ} : f i = f j ↔ i % m = j % m := by
  constructor
  · intro hij
    rw [h.eq_mod i, h.eq_mod j] at hij
    exact h.inj _ _ (Nat.mod_lt _ h.pos) (Nat.mod_lt _ h.pos) hij
  · intro hij
    rw [h.eq_mod i, h.eq_mod j, hij]

lemma eq_succ (h : CycArr G m f) {i j : ℕ} (hij : f i = f j) : f (i + 1) = f (j + 1) := by
  rw [h.eq_iff] at hij ⊢
  exact Nat.ModEq.add_right 1 hij

lemma rotate (h : CycArr G m f) (a : ℕ) : CycArr G m (fun i => f (a + i)) where
  three_le := h.three_le
  periodic i := by rw [← Nat.add_assoc, h.periodic]
  inj i j hi hj hij := by
    rw [h.eq_iff] at hij
    have := Nat.ModEq.add_left_cancel' a hij
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  adj i := h.adj (a + i)

lemma succ_mod_of_lt {i : ℕ} (hc : i % m + 1 < m) : (i + 1) % m = i % m + 1 := by
  have h1 := Nat.mod_add_div i m
  have : i + 1 = (i % m + 1) + m * (i / m) := by omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

lemma succ_mod_of_eq {i : ℕ} (hc : i % m + 1 = m) : (i + 1) % m = 0 := by
  have h1 := Nat.mod_add_div i m
  have : i + 1 = m * (i / m + 1) := by rw [Nat.mul_succ]; omega
  rw [this, Nat.mul_mod_right]

/-- Build a cyclic arrangement from a function on `[0, m]` with `h m = h 0`. -/
lemma of_fun {h : ℕ → V} (hm : 3 ≤ m) (hinj : ∀ i j, i < m → j < m → h i = h j → i = j)
    (hadj : ∀ i < m, G.Adj (h i) (h (i + 1))) (hend : h m = h 0) :
    CycArr G m (fun i => h (i % m)) where
  three_le := hm
  periodic i := by simp
  inj i j hi hj hij := by
    simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hij
    exact hinj i j hi hj hij
  adj i := by
    have hm0 : 0 < m := by omega
    have hlt : i % m < m := Nat.mod_lt _ hm0
    by_cases hc : i % m + 1 < m
    · rw [succ_mod_of_lt hc]
      exact hadj _ hlt
    · have hc' : i % m + 1 = m := by omega
      rw [succ_mod_of_eq hc', ← hend]
      have := hadj _ hlt
      rwa [hc'] at this

end CycArr

/-- The walk `f 0, f 1, …, f n`. -/
def walkOf (G : SimpleGraph V) (f : ℕ → V) (hf : ∀ i, G.Adj (f i) (f (i + 1))) :
    (n : ℕ) → G.Walk (f 0) (f n)
  | 0 => Walk.nil
  | n + 1 => (walkOf G f hf n).concat (hf n)

lemma support_walkOf (G : SimpleGraph V) (f : ℕ → V) (hf : ∀ i, G.Adj (f i) (f (i + 1)))
    (n : ℕ) : (walkOf G f hf n).support = (List.range (n + 1)).map f := by
  induction n with
  | zero => simp [walkOf]
  | succ n ih =>
    rw [walkOf, Walk.support_concat, ih]
    conv_rhs => rw [List.range_succ]
    simp

lemma edges_walkOf (G : SimpleGraph V) (f : ℕ → V) (hf : ∀ i, G.Adj (f i) (f (i + 1)))
    (n : ℕ) : (walkOf G f hf n).edges = (List.range n).map (fun i => s(f i, f (i + 1))) := by
  induction n with
  | zero => simp [walkOf]
  | succ n ih =>
    rw [walkOf, Walk.edges_concat, ih]
    conv_rhs => rw [List.range_succ]
    simp

lemma length_walkOf (G : SimpleGraph V) (f : ℕ → V) (hf : ∀ i, G.Adj (f i) (f (i + 1)))
    (n : ℕ) : (walkOf G f hf n).length = n := by
  induction n with
  | zero => simp [walkOf]
  | succ n ih => rw [walkOf, Walk.length_concat, ih]

namespace CycArr

variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}

/-- A cyclic arrangement gives a cycle of the same length. -/
lemma exists_isCycle (h : CycArr G m f) :
    ∃ c : G.Walk (f 0) (f 0), c.IsCycle ∧ c.length = m := by
  have hm := h.three_le
  have hend : f (m - 1 + 1) = f 0 := by
    rw [show m - 1 + 1 = 0 + m by omega, h.periodic]
  let p := (walkOf G (fun i => f (i + 1)) (fun i => h.adj (i + 1)) (m - 1)).copy rfl hend
  refine ⟨Walk.cons (h.adj 0) p, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    constructor
    · rw [Walk.isPath_def, Walk.support_copy, support_walkOf]
      refine List.Nodup.map_on ?_ List.nodup_range
      intro i hi j hj hij
      simp only [List.mem_range] at hi hj
      rw [h.eq_iff] at hij
      have := Nat.ModEq.add_right_cancel' 1 hij
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    · rw [Walk.edges_copy, edges_walkOf]
      simp only [List.mem_map, List.mem_range, not_exists, not_and]
      intro i hi he
      rw [Sym2.eq_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := h.inj _ _ (by omega) (by omega) h1
        omega
      · have := h.inj _ _ (by omega) (by omega) h1
        have h3 : i = 0 := by omega
        subst h3
        have := h.inj _ _ (by omega) (by omega) h2
        omega
  · simp only [Walk.length_cons, p, Walk.length_copy, length_walkOf]
    omega

/-- A cyclic arrangement through all vertices gives a Hamiltonian graph. -/
lemma isHamiltonian [Fintype V] [DecidableEq V] (h : CycArr G m f)
    (hm : m = Fintype.card V) : G.IsHamiltonian := by
  intro _
  obtain ⟨c, hc, hl⟩ := h.exists_isCycle
  exact ⟨f 0, c, Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.2 ⟨hc, hl.trans hm⟩⟩

/-- In a cyclic arrangement `m ≤ |V|`. -/
lemma le_card [Fintype V] (h : CycArr G m f) : m ≤ Fintype.card V := by
  classical
  have : ((Finset.range m).image f).card = m := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact h.inj i j (by simpa using hi) (by simpa using hj) hij
  rw [← this]
  exact Finset.card_le_univ _

end CycArr

/-- A cycle gives a cyclic arrangement of the same length. -/
lemma cycArr_of_isCycle {G : SimpleGraph V} {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    CycArr G c.length (fun i => c.getVert (i % c.length)) := by
  have h3 := hc.three_le_length
  refine CycArr.of_fun h3 ?_ (fun i hi => c.adj_getVert_succ hi) (by simp)
  intro i j hi hj hij
  exact hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) hij

/-- A Hamiltonian graph on at least three vertices has a cyclic arrangement through all
vertices. -/
lemma exists_cycArr_of_isHamiltonian [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsHamiltonian) (hn : 3 ≤ Fintype.card V) :
    ∃ f, CycArr G (Fintype.card V) f := by
  obtain ⟨a, c, hc⟩ := hG (by omega)
  have := cycArr_of_isCycle hc.isCycle
  rw [hc.length_eq] at this
  exact ⟨_, this⟩

/-- A graph in which any two distinct vertices are adjacent is Hamiltonian (if it has at least
three vertices). -/
lemma isHamiltonian_of_forall_adj [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hn : 3 ≤ Fintype.card V) (hadj : ∀ u v, u ≠ v → G.Adj u v) : G.IsHamiltonian := by
  set n := Fintype.card V
  have hn0 : 0 < n := by omega
  let e := Fintype.equivFin V
  let h : ℕ → V := fun i => e.symm ⟨i % n, Nat.mod_lt _ hn0⟩
  have hinj : ∀ i j, h i = h j → i % n = j % n := by
    intro i j hij
    have := e.symm.injective hij
    simpa using this
  refine CycArr.isHamiltonian (m := n) (f := h) ⟨hn, ?_, ?_, ?_⟩ rfl
  · intro i
    simp [h]
  · intro i j hi hj hij
    have := hinj i j hij
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · intro i
    apply hadj
    intro hij
    have := hinj i (i + 1) hij
    have hlt : i % n < n := Nat.mod_lt _ hn0
    by_cases hc : i % n + 1 < n
    · rw [CycArr.succ_mod_of_lt hc] at this
      omega
    · rw [CycArr.succ_mod_of_eq (by omega)] at this
      omega

end Hamiltonicity
