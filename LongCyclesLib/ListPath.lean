/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import MengerHamilton.ChvatalErdosAux

/-!
# Paths and cycles as vertex lists

Auxiliary material for `LongCyclesLib.LongCycles`: paths are handled as lists of vertices (`List.IsChain`
of the adjacency relation, without repetitions), and converted to Mathlib's walks at the end.
-/

@[expose] public section

open SimpleGraph

namespace LongCycles

variable {W : Type*}

/-- The list `x i, x (i + 1), …, x (i + n - 1)`. -/
def seg (x : ℕ → W) (i n : ℕ) : List W := (List.range' i n).map x

section seg

variable (x : ℕ → W) (i n : ℕ)

@[simp] lemma length_seg : (seg x i n).length = n := by simp [seg]

lemma mem_seg {y : W} : y ∈ seg x i n ↔ ∃ t, i ≤ t ∧ t < i + n ∧ x t = y := by
  simp only [seg, List.mem_map, List.mem_range']
  constructor
  · rintro ⟨t, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨i + 1 * s, by omega, by omega, rfl⟩
  · rintro ⟨t, h1, h2, rfl⟩
    exact ⟨t, ⟨t - i, by omega, by omega⟩, rfl⟩

lemma getElem_seg {t : ℕ} (ht : t < (seg x i n).length) : (seg x i n)[t] = x (i + t) := by
  simp [seg]

lemma isChain_seg {G : SimpleGraph W} (h : ∀ t, i ≤ t → t + 1 < i + n → G.Adj (x t) (x (t + 1))) :
    (seg x i n).IsChain G.Adj := by
  rw [List.isChain_iff_getElem]
  intro t ht
  rw [getElem_seg, getElem_seg]
  simp only [length_seg] at ht
  rw [← Nat.add_assoc]
  exact h _ (by omega) (by omega)

lemma nodup_seg (h : ∀ s t, i ≤ s → s < i + n → i ≤ t → t < i + n → x s = x t → s = t) :
    (seg x i n).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro a b hab
  simp only [List.get_eq_getElem, getElem_seg] at hab
  have ha := a.2
  have hb := b.2
  simp only [length_seg] at ha hb
  have := h _ _ (by omega) (by omega) (by omega) (by omega) hab
  exact Fin.ext (by omega)

lemma head?_seg (hn : 0 < n) : (seg x i n).head? = some (x i) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [seg, List.range'_succ]

lemma getLast?_seg (hn : 0 < n) : (seg x i n).getLast? = some (x (i + n - 1)) := by
  rw [List.getLast?_eq_getElem?]
  simp only [length_seg]
  rw [List.getElem?_eq_getElem (by simp; omega), getElem_seg]
  congr 2
  omega

end seg

section graph

variable {G : SimpleGraph W}

lemma isChain_reverse_adj {l : List W} : l.reverse.IsChain G.Adj ↔ l.IsChain G.Adj := by
  rw [List.isChain_reverse]
  exact ⟨fun h => h.imp fun _ _ h => h.symm, fun h => h.imp fun _ _ h => h.symm⟩

/-- A list without repetitions, with consecutive entries adjacent and the last entry adjacent to
the first, of length at least three, gives a cyclic arrangement. -/
lemma exists_cycArr_of_list (l : List W) (hl : 3 ≤ l.length) (hc : l.IsChain G.Adj)
    (hnd : l.Nodup) (hcl : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, G.Adj a b) :
    ∃ g, Hamiltonicity.CycArr G l.length g ∧ (∀ i, g i ∈ l) ∧ ∀ y ∈ l, ∃ i, g i = y := by
  set L := l.length with hL
  have hL0 : 0 < L := by omega
  set d := l[0]'hL0 with hd
  set h : ℕ → W := fun i => l.getD i d with hh
  have hlt : ∀ i (hi : i < L), h i = l[i] := fun i hi => List.getD_eq_getElem _ _ hi
  have hm : h L = h 0 := by
    rw [hlt 0 hL0]
    exact List.getD_eq_default _ _ le_rfl
  refine ⟨_, Hamiltonicity.CycArr.of_fun (h := h) hl ?_ ?_ hm, ?_, ?_⟩
  · intro i j hi hj hij
    rw [hlt i hi, hlt j hj] at hij
    exact (hnd.getElem_inj_iff).1 hij
  · intro i hi
    by_cases hi1 : i + 1 < L
    · rw [hlt i hi, hlt (i + 1) hi1]
      exact hc.getElem i hi1
    · have hiL : i + 1 = L := by omega
      rw [hiL, hm, hlt i hi, hlt 0 hL0]
      apply hcl
      · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
        simp only [Option.mem_def, Option.some.injEq]
        congr 1
        omega
      · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hL0]
        rfl
  · intro i
    rw [hlt _ (Nat.mod_lt _ hL0)]
    exact List.getElem_mem _
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    exact ⟨i, by rw [Nat.mod_eq_of_lt hi, hlt i hi]⟩

/-- A cycle from a vertex list. -/
lemma exists_cycle_of_list (l : List W) (hl : 3 ≤ l.length) (hc : l.IsChain G.Adj)
    (hnd : l.Nodup) (hcl : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, G.Adj a b) :
    ∃ (u : W) (c : G.Walk u u), c.IsCycle ∧ c.length = l.length := by
  obtain ⟨g, hg, -, -⟩ := exists_cycArr_of_list l hl hc hnd hcl
  obtain ⟨c, hc, hlen⟩ := hg.exists_isCycle
  exact ⟨_, c, hc, hlen⟩

/-- Two paths between distinct vertices `u` and `v` meeting only at their ends form a cycle. -/
lemma exists_cycle_of_two_paths {u v : W} (huv : u ≠ v) (p q : List W)
    (hp : p.IsChain G.Adj) (hq : q.IsChain G.Adj) (hpn : p.Nodup) (hqn : q.Nodup)
    (hph : p.head? = some u) (hpl : p.getLast? = some v)
    (hqh : q.head? = some v) (hql : q.getLast? = some u)
    (hdisj : ∀ y ∈ p, y ∈ q → y = u ∨ y = v) (hlen : 3 ≤ p.length + q.length - 2) :
    ∃ (w : W) (c : G.Walk w w), c.IsCycle ∧ c.length = p.length + q.length - 2 := by
  obtain ⟨q1, rfl⟩ : ∃ q1, q = v :: q1 := by
    cases q with
    | nil => simp at hqh
    | cons a q1 => simp only [List.head?_cons, Option.some.injEq] at hqh; exact ⟨q1, hqh ▸ rfl⟩
  have hq1 : q1 ≠ [] := by
    rintro rfl
    simp only [List.getLast?_singleton, Option.some.injEq] at hql
    exact huv hql.symm
  obtain ⟨q2, hq2⟩ : ∃ q2, q1 = q2 ++ [u] := by
    refine ⟨q1.dropLast, ?_⟩
    have := List.dropLast_append_getLast hq1
    rw [List.getLast?_cons, List.getLast?_eq_some_getLast hq1] at hql
    simp only [Option.getD_some, Option.some.injEq] at hql
    rw [← hql]
    exact this.symm
  subst hq2
  have hqn' := hqn
  rw [List.nodup_cons, List.nodup_append] at hqn'
  obtain ⟨hvq, hq2n, -, hq2u⟩ := hqn'
  simp only [List.mem_append, List.mem_singleton, not_or] at hvq
  have hq2u' : u ∉ q2 := fun h => hq2u u h u (List.mem_singleton_self _) rfl
  have hlenq : (v :: (q2 ++ [u])).length = q2.length + 2 := by simp
  rw [hlenq] at hlen ⊢
  suffices h3 : (p ++ q2).IsChain G.Adj ∧ (p ++ q2).Nodup ∧
      ∀ a ∈ (p ++ q2).getLast?, ∀ b ∈ (p ++ q2).head?, G.Adj a b by
    obtain ⟨w, c, hc, hcl⟩ := exists_cycle_of_list (G := G) (p ++ q2) (by simp; omega)
      h3.1 h3.2.1 h3.2.2
    exact ⟨w, c, hc, by rw [hcl, List.length_append]; omega⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [List.isChain_append]
    refine ⟨hp, (hq.infix ⟨[v], [u], by simp⟩), ?_⟩
    intro a ha b hb
    rw [hpl, Option.mem_def, Option.some.injEq] at ha
    subst ha
    cases q2 with
    | nil => simp at hb
    | cons c q3 =>
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb
      simp only [List.cons_append] at hq
      exact (List.isChain_cons_cons.1 hq).1
  · rw [List.nodup_append]
    refine ⟨hpn, hq2n, fun a ha b hb hab => ?_⟩
    subst hab
    rcases hdisj a ha (by simp [hb]) with rfl | rfl
    · exact hq2u' hb
    · exact hvq.1 hb
  · intro a ha b hb
    rw [List.head?_append, hph] at hb
    simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hb
    subst hb
    rw [List.getLast?_append] at ha
    cases hq2l : q2.getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at hq2l
      subst hq2l
      rw [hpl] at ha
      simp only [List.getLast?_nil, Option.none_or, Option.mem_def, Option.some.injEq] at ha
      subst ha
      simp only [List.nil_append] at hq
      exact (List.isChain_cons_cons.1 hq).1
    | some c =>
      rw [hq2l] at ha
      simp only [Option.some_or, Option.mem_def, Option.some.injEq] at ha
      subst ha
      have := hq.infix (l₁ := q2 ++ [u]) ⟨[v], [], by simp⟩
      rw [List.isChain_append] at this
      exact this.2.2 _ hq2l _ rfl

/-- A list with consecutive entries adjacent is the support of a walk. -/
lemma exists_walk_of_list : ∀ (l : List W) {u v : W}, l.IsChain G.Adj →
    l.head? = some u → l.getLast? = some v → ∃ p : G.Walk u v, p.support = l
  | [], _, _, _, h, _ => by simp at h
  | [a], u, v, _, hh, hl => by
    simp only [List.head?_cons, Option.some.injEq] at hh
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hh hl
    exact ⟨Walk.nil, rfl⟩
  | a :: b :: l, u, v, hc, hh, hl => by
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    rw [List.isChain_cons_cons] at hc
    obtain ⟨p, hp⟩ := exists_walk_of_list (b :: l) hc.2 rfl
      (by rwa [List.getLast?_cons_cons] at hl)
    exact ⟨Walk.cons hc.1 p, by simp [hp]⟩

/-- A list path gives a walk which is a path. -/
lemma exists_path_of_list (l : List W) {u v : W} (hc : l.IsChain G.Adj) (hnd : l.Nodup)
    (hh : l.head? = some u) (hl : l.getLast? = some v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length + 1 = l.length := by
  obtain ⟨p, hp⟩ := exists_walk_of_list l hc hh hl
  refine ⟨p, ?_, ?_⟩
  · rw [Walk.isPath_def, hp]; exact hnd
  · rw [← hp, Walk.length_support]

/-- In a list starting in `Lo` and ending in `Hi` (disjoint), some contiguous piece starts in
`Lo`, ends in `Hi` and has its interior outside `Lo ∪ Hi`. -/
lemma exists_bridge (Lo Hi : W → Prop) (hdisj : ∀ y, Lo y → ¬ Hi y) :
    ∀ (l : List W), (∃ a ∈ l.head?, Lo a) → (∃ b ∈ l.getLast?, Hi b) →
    ∃ u v I, Lo u ∧ Hi v ∧ (∀ y ∈ I, ¬ Lo y ∧ ¬ Hi y) ∧ (u :: (I ++ [v])) <:+: l := by
  classical
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  intro ⟨a, ha, hLa⟩ ⟨b, hb, hHb⟩
  obtain ⟨rest, rfl⟩ : ∃ rest, l = a :: rest := by
    cases l with
    | nil => simp at ha
    | cons c r =>
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      exact ⟨r, ha ▸ rfl⟩
  set P : W → Bool := fun y => decide (¬ Lo y ∧ ¬ Hi y) with hP
  have hsplit := List.takeWhile_append_dropWhile (p := P) (l := rest)
  cases hpost : rest.dropWhile P with
  | nil =>
    exfalso
    rw [List.dropWhile_eq_nil_iff] at hpost
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hb
      subst hb
      exact hdisj _ hLa hHb
    | cons c r =>
      rw [List.getLast?_cons_cons] at hb
      have hbm : b ∈ c :: r := List.mem_of_mem_getLast? hb
      have := hpost b hbm
      simp only [hP, decide_eq_true_eq] at this
      exact this.2 hHb
  | cons e post =>
    have hne : ¬ (¬ Lo e ∧ ¬ Hi e) := by
      have h1 := List.head_dropWhile_not P (l := rest) (by rw [hpost]; simp)
      have h2 : (rest.dropWhile P).head (by rw [hpost]; simp) = e := by simp [hpost]
      rw [h2] at h1
      simpa [hP] using h1
    have hpre : ∀ y ∈ rest.takeWhile P, ¬ Lo y ∧ ¬ Hi y := by
      intro y hy
      have := List.mem_takeWhile_imp hy
      simpa [hP] using this
    rw [hpost] at hsplit
    by_cases hHe : Hi e
    · refine ⟨a, e, rest.takeWhile P, hLa, hHe, hpre, ?_⟩
      refine ⟨[], post, ?_⟩
      conv_rhs => rw [← hsplit]
      simp
    · have hLe : Lo e := by
        by_contra h
        exact hne ⟨h, hHe⟩
      have hlen : (e :: post).length < n := by
        have := List.length_dropWhile_le P rest
        rw [hpost] at this
        simp only [List.length_cons] at hn this ⊢
        omega
      have hb' : b ∈ (e :: post).getLast? := by
        rw [Option.mem_def] at hb ⊢
        rw [← hb, ← hsplit]
        cases h : List.takeWhile P rest <;> simp [List.getLast?_append, List.getLast?_cons]
      obtain ⟨u, v, I, hu, hv, hI, hinf⟩ := ih _ hlen (e :: post) rfl ⟨e, rfl, hLe⟩ ⟨b, hb', hHb⟩
      refine ⟨u, v, I, hu, hv, hI, hinf.trans ?_⟩
      refine ⟨a :: rest.takeWhile P, [], ?_⟩
      conv_rhs => rw [← hsplit]
      simp

end graph

end LongCycles
