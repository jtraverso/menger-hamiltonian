/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LongCyclesLib.DiracCore

/-!
# Dirac's long cycle lemma

`LongCycles.dirac_long_cycle`: **Dirac (1952).** In a finite graph in which no single vertex
separates two others, every cycle-length bound `k ≤ n` with `k ≤ 2 δ` is attained: there is a
cycle of length at least `k`. The proof uses a longest path `x 0, …, x m`: crossing neighbours of
the ends close a cycle through the whole path (which is then Hamiltonian), "overlapping" neighbours
give a cycle through both neighbourhoods, and otherwise `LongCycles.core_cycle` applies.
-/

@[expose] public section

open SimpleGraph

namespace LongCycles

variable {W : Type*} {H : SimpleGraph W}

lemma PathFn.reverse {m : ℕ} {x : ℕ → W} (hx : PathFn H m x) : PathFn H m (fun i => x (m - i)) where
  inj i j hi hj h := by have := hx.inj _ _ (by omega) (by omega) h; omega
  adj i hi := by
    have := hx.adj (m - (i + 1)) (by omega)
    rw [show m - (i + 1) + 1 = m - i by omega] at this
    exact this.symm

lemma PathFn.card_le [Fintype W] {m : ℕ} {x : ℕ → W} (hx : PathFn H m x) :
    m + 1 ≤ Fintype.card W := by
  classical
  have : ((Finset.range (m + 1)).image x).card = m + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj h
    exact hx.inj i j (by simp at hi; omega) (by simp at hj; omega) h
  rw [← this]
  exact Finset.card_le_univ _

/-- Existence of a longest path. -/
lemma exists_longest [Finite W] [Nonempty W] :
    ∃ m x, PathFn H m x ∧ ∀ m' x', PathFn H m' x' → m' ≤ m := by
  classical
  have := Fintype.ofFinite W
  obtain ⟨v⟩ := ‹Nonempty W›
  have h0 : PathFn H 0 (fun _ => v) := ⟨fun i j hi hj _ => by omega, fun i hi => by omega⟩
  set M := Nat.findGreatest (fun m => ∃ x, PathFn H m x) (Fintype.card W)
  obtain ⟨x, hx⟩ : ∃ x, PathFn H M x :=
    Nat.findGreatest_spec (P := fun m => ∃ x, PathFn H m x) (Nat.zero_le _) ⟨_, h0⟩
  refine ⟨M, x, hx, fun m' x' hx' => ?_⟩
  exact Nat.le_findGreatest (P := fun m => ∃ x, PathFn H m x) (by have := hx'.card_le; omega)
    ⟨x', hx'⟩

/-- In a longest path, all neighbours of the first vertex lie on the path. -/
lemma nbr_on_path {m : ℕ} {x : ℕ → W} (hx : PathFn H m x)
    (hmax : ∀ m' x', PathFn H m' x' → m' ≤ m) {y : W} (hy : H.Adj (x 0) y) :
    ∃ i ≤ m, x i = y := by
  by_contra hno
  push Not at hno
  have : PathFn H (m + 1) (fun i => if i = 0 then y else x (i - 1)) := by
    constructor
    · intro i j hi hj h
      by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0 <;> simp only [hi0, hj0, ↓reduceIte] at h
      · omega
      · exact absurd h.symm (hno _ (by omega))
      · exact absurd h (hno _ (by omega))
      · have := hx.inj _ _ (by omega) (by omega) h; omega
    · intro i hi
      by_cases hi0 : i = 0
      · subst hi0; simpa using hy.symm
      · simp only [hi0, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
        have := hx.adj (i - 1) (by omega)
        rwa [show i - 1 + 1 = i + 1 - 1 by omega] at this
  have := hmax _ _ this
  omega

/-- The lollipop lemma: if `x 0` is adjacent to `x i` for all `i ∈ A ⊆ [1, a]`, `a ∈ A`, then
every `x μ` with `μ < a` is joined to `x a` by a path inside `x 0, …, x a` with more than `|A|`
vertices. -/
lemma lollipop (x : ℕ → W) (a : ℕ) (hinj : ∀ i j, i ≤ a → j ≤ a → x i = x j → i = j)
    (hadj : ∀ i, i < a → H.Adj (x i) (x (i + 1))) (A : Finset ℕ)
    (hA : ∀ i ∈ A, 1 ≤ i ∧ i ≤ a ∧ H.Adj (x 0) (x i)) (ha : a ∈ A) (μ : ℕ) (hμ : μ < a) :
    ∃ l : List W, l.head? = some (x μ) ∧ l.getLast? = some (x a) ∧ l.IsChain H.Adj ∧ l.Nodup ∧
      (∀ y ∈ l, ∃ i ≤ a, x i = y) ∧ A.card + 1 ≤ l.length := by
  classical
  have hne : (A.filter (μ < ·)).Nonempty := ⟨a, by simp [ha, hμ]⟩
  set r := (A.filter (μ < ·)).min' hne with hr
  have hrA : r ∈ A ∧ μ < r := by
    have : r ∈ A.filter (μ < ·) := Finset.min'_mem _ hne
    simpa using this
  have hrmin : ∀ i ∈ A, μ < i → r ≤ i := fun i hi hμi =>
    Finset.min'_le _ _ (by simp [hi, hμi])
  have hra : r ≤ a := (hA r hrA.1).2.1
  set l1 := (seg x 0 (μ + 1)).reverse
  set l2 := seg x r (a - r + 1)
  refine ⟨l1 ++ l2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [head?_of_append_ne (by simp [l1, ← List.length_pos_iff]), List.head?_reverse,
      getLast?_seg _ _ _ (by omega)]
    simp
  · rw [getLast?_of_append_ne (by simp [l2, ← List.length_pos_iff]), getLast?_seg _ _ _ (by omega)]
    congr 2; omega
  · rw [List.isChain_append]
    refine ⟨isChain_reverse_adj.2 (isChain_seg _ _ _ fun t _ ht => hadj t (by omega)),
      isChain_seg _ _ _ fun t _ ht => hadj t (by omega), ?_⟩
    intro u hu v hv
    rw [List.getLast?_reverse, head?_seg _ _ _ (by omega), Option.mem_def,
      Option.some.injEq] at hu
    rw [head?_seg _ _ _ (by omega), Option.mem_def, Option.some.injEq] at hv
    subst hu hv
    exact (hA r hrA.1).2.2
  · rw [List.nodup_append]
    refine ⟨List.nodup_reverse.2 (nodup_seg _ _ _ fun s t _ hs _ ht h =>
      hinj s t (by omega) (by omega) h), nodup_seg _ _ _ fun s t _ hs _ ht h =>
      hinj s t (by omega) (by omega) h, ?_⟩
    intro u hu v hv huv
    subst huv
    rw [List.mem_reverse, mem_seg] at hu
    rw [mem_seg] at hv
    obtain ⟨s, -, hs, rfl⟩ := hu
    obtain ⟨t, ht1, ht2, ht⟩ := hv
    have := hinj _ _ (by omega) (by omega) ht
    omega
  · intro y hy
    rw [List.mem_append, List.mem_reverse, mem_seg, mem_seg] at hy
    rcases hy with ⟨t, -, ht, rfl⟩ | ⟨t, -, ht, rfl⟩
    · exact ⟨t, by omega, rfl⟩
    · exact ⟨t, by omega, rfl⟩
  · simp only [List.length_append, List.length_reverse, length_seg, l1, l2]
    have hsub : A ⊆ Finset.Icc 1 μ ∪ Finset.Icc r a := by
      intro i hi
      obtain ⟨h1, h2, -⟩ := hA i hi
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
      by_cases hiμ : i ≤ μ
      · exact Or.inl ⟨h1, hiμ⟩
      · exact Or.inr ⟨hrmin i hi (by omega), h2⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simp only [Nat.card_Icc] at this
    omega

/-- A walk from outside a set to inside it crosses it along an edge. -/
lemma exists_adj_cross (S : W → Prop) : ∀ {u v : W}, H.Walk u v → ¬ S u → S v →
    ∃ a b, H.Adj a b ∧ ¬ S a ∧ S b
  | _, _, .nil, hu, hv => absurd hv hu
  | _, _, .cons (v := w) h p, hu, hv => by
    by_cases hw : S w
    · exact ⟨_, _, h, hu, hw⟩
    · exact exists_adj_cross S p hw hv

end LongCycles

namespace LongCycles

variable {W : Type*}

/-- **Dirac's long cycle lemma (1952).** Let `H` be a finite graph in which no single vertex
separates two others. If `3 ≤ k ≤ |W|` and every vertex has degree at least `k / 2`, then `H`
has a cycle of length at least `k`. -/
theorem dirac_long_cycle [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    {k : ℕ} (hk : 3 ≤ k) (hn : k ≤ Fintype.card W) (hdeg : ∀ v, k ≤ 2 * H.degree v)
    (hconn : ∀ w y z : W, y ≠ w → z ≠ w → ∃ p : H.Walk y z, w ∉ p.support) :
    ∃ (u : W) (c : H.Walk u u), c.IsCycle ∧ k ≤ c.length := by
  classical
  have hne : Nonempty W := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨m, x, hx, hmax⟩ := exists_longest (H := H)
  have hnb0 : ∀ y, H.Adj (x 0) y → ∃ i ≤ m, x i = y := fun y hy => nbr_on_path hx hmax hy
  have hnbm : ∀ y, H.Adj (x m) y → ∃ i ≤ m, x i = y := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := nbr_on_path hx.reverse hmax (y := y) (by simpa using hy)
    exact ⟨m - i, by omega, rfl⟩
  set A := (Finset.range (m + 1)).filter (fun i => H.Adj (x 0) (x i)) with hA
  set B := (Finset.range (m + 1)).filter (fun i => H.Adj (x m) (x i)) with hB
  have hcardnb : ∀ j ≤ m, (∀ y, H.Adj (x j) y → ∃ i ≤ m, x i = y) →
      ((Finset.range (m + 1)).filter (fun i => H.Adj (x j) (x i))).card = H.degree (x j) := by
    intro j hj hnb
    rw [← card_neighborFinset_eq_degree]
    have : H.neighborFinset (x j) =
        ((Finset.range (m + 1)).filter (fun i => H.Adj (x j) (x i))).image x := by
      ext y
      simp only [mem_neighborFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · intro hy
        obtain ⟨i, hi, rfl⟩ := hnb y hy
        exact ⟨i, ⟨by omega, hy⟩, rfl⟩
      · rintro ⟨i, ⟨_, hi⟩, rfl⟩
        exact hi
    rw [this, Finset.card_image_of_injOn]
    intro i hi j' hj' h
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj'
    exact hx.inj i j' (by omega) (by omega) h
  have hAcard : A.card = H.degree (x 0) := hcardnb 0 (Nat.zero_le _) hnb0
  have hBcard : B.card = H.degree (x m) := hcardnb m le_rfl hnbm
  have hAi : ∀ i ∈ A, 1 ≤ i ∧ i ≤ m ∧ H.Adj (x 0) (x i) := by
    intro i hi
    simp only [hA, Finset.mem_filter, Finset.mem_range] at hi
    refine ⟨?_, by omega, hi.2⟩
    by_contra h0
    obtain rfl : i = 0 := by omega
    exact H.irrefl hi.2
  have hBi : ∀ i ∈ B, i < m ∧ H.Adj (x m) (x i) := by
    intro i hi
    simp only [hB, Finset.mem_filter, Finset.mem_range] at hi
    refine ⟨?_, hi.2⟩
    by_contra h0
    obtain rfl : i = m := by omega
    exact H.irrefl hi.2
  have hKA : k ≤ 2 * A.card := hAcard ▸ hdeg _
  have hKB : k ≤ 2 * B.card := hBcard ▸ hdeg _
  have hAne : A.Nonempty := Finset.card_pos.1 (by omega)
  have hBne : B.Nonempty := Finset.card_pos.1 (by omega)
  set a := A.max' hAne with ha_def
  set b := B.min' hBne with hb_def
  have ha : a ∈ A := Finset.max'_mem _ _
  have hb : b ∈ B := Finset.min'_mem _ _
  have hamax : ∀ i ∈ A, i ≤ a := fun i hi => Finset.le_max' _ _ hi
  have hbmin : ∀ i ∈ B, b ≤ i := fun i hi => Finset.min'_le _ _ hi
  have hm2 : 2 ≤ m := by
    have : A ⊆ Finset.Icc 1 m := fun i hi => by
      obtain ⟨h1, h2, -⟩ := hAi i hi
      simp [h1, h2]
    have := Finset.card_le_card this
    simp only [Nat.card_Icc] at this
    omega
  by_cases hcross : ∃ t, t < m ∧ H.Adj (x 0) (x (t + 1)) ∧ H.Adj (x m) (x t)
  · obtain ⟨t, htm, h0, hm⟩ := hcross
    set l := seg x 0 (t + 1) ++ (seg x (t + 1) (m - t)).reverse with hl
    have hlen : l.length = m + 1 := by simp [hl]; omega
    have hlmem : ∀ y ∈ l, ∃ i ≤ m, x i = y := by
      intro y hy
      rw [hl, List.mem_append, List.mem_reverse, mem_seg, mem_seg] at hy
      rcases hy with ⟨i, -, hi, rfl⟩ | ⟨i, -, hi, rfl⟩
      · exact ⟨i, by omega, rfl⟩
      · exact ⟨i, by omega, rfl⟩
    have h3 : l.IsChain H.Adj ∧ l.Nodup ∧ ∀ u ∈ l.getLast?, ∀ v ∈ l.head?, H.Adj u v := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hl, List.isChain_append]
        refine ⟨isChain_seg _ _ _ fun i _ hi => hx.adj i (by omega),
          isChain_reverse_adj.2 (isChain_seg _ _ _ fun i _ hi => hx.adj i (by omega)), ?_⟩
        intro u hu v hv
        rw [getLast?_seg _ _ _ (by omega), Option.mem_def, Option.some.injEq] at hu
        rw [List.head?_reverse, getLast?_seg _ _ _ (by omega), Option.mem_def,
          Option.some.injEq] at hv
        subst hu hv
        rw [show 0 + (t + 1) - 1 = t by omega, show t + 1 + (m - t) - 1 = m by omega]
        exact hm.symm
      · rw [hl, List.nodup_append]
        refine ⟨nodup_seg _ _ _ fun i j _ hi _ hj h => hx.inj i j (by omega) (by omega) h,
          List.nodup_reverse.2 (nodup_seg _ _ _ fun i j _ hi _ hj h =>
            hx.inj i j (by omega) (by omega) h), ?_⟩
        intro u hu v hv huv
        subst huv
        obtain ⟨i, -, hi, rfl⟩ := (mem_seg _ _ _).1 hu
        obtain ⟨j, hj1, hj2, hj⟩ := (mem_seg _ _ _).1 (List.mem_reverse.1 hv)
        have := hx.inj _ _ (by omega) (by omega) hj
        omega
      · intro u hu v hv
        rw [hl, getLast?_of_append_ne (by simp [seg]; omega), List.getLast?_reverse,
          head?_seg _ _ _ (by omega), Option.mem_def, Option.some.injEq] at hu
        rw [hl, head?_of_append_ne (by simp [seg]), head?_seg _ _ _ (by omega), Option.mem_def,
          Option.some.injEq] at hv
        subst hu hv
        exact h0.symm
    obtain ⟨g, hg, hgl, hlg⟩ := exists_cycArr_of_list l (by omega) h3.1 h3.2.1 h3.2.2
    rw [hlen] at hg
    by_cases hfull : m + 1 = Fintype.card W
    · obtain ⟨c, hc, hclen⟩ := hg.exists_isCycle
      exact ⟨_, c, hc, by omega⟩
    exfalso
    obtain ⟨y, hy⟩ : ∃ y, y ∉ l := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset W) ⊆ l.toFinset := fun y _ => List.mem_toFinset.2 (h y)
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, List.toFinset_card_of_nodup h3.2.1, hlen] at this
      have := hx.card_le
      omega
    obtain ⟨w, hwy, hw0⟩ : ∃ w, w ≠ y ∧ w ≠ x 0 := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset W) ⊆ {y, x 0} := fun w _ => by
        by_cases hw : w = y
        · simp [hw]
        · simp [h w hw]
      have := (Finset.card_le_card hsub).trans (Finset.card_le_two)
      rw [Finset.card_univ] at this
      omega
    obtain ⟨p, -⟩ := hconn w y (x 0) (Ne.symm hwy) (Ne.symm hw0)
    obtain ⟨a', b', hab', ha', hb'⟩ := exists_adj_cross (· ∈ l) p hy
      (by
        rw [hl]
        simp only [seg, List.mem_append, List.mem_map, List.mem_range'_1, zero_le, zero_add,
          Order.lt_add_one_iff, true_and, List.mem_reverse, Order.add_one_le_iff]
        exact Or.inl ⟨0, by omega, rfl⟩)
    obtain ⟨j, rfl⟩ := hlg b' hb'
    have hnew : PathFn H (m + 1) (fun i => if i = 0 then a' else g (j + i - 1)) := by
      constructor
      · intro i i' hi hi' h
        by_cases hi0 : i = 0 <;> by_cases hi'0 : i' = 0 <;> simp only [hi0, hi'0, ↓reduceIte] at h
        · omega
        · exact absurd (h ▸ hgl _) ha'
        · exact absurd (h ▸ hgl _) ha'
        · rw [hg.eq_iff] at h
          have := Nat.ModEq.add_left_cancel' j (show j + (i - 1) ≡ j + (i' - 1) [MOD m + 1] by
            rw [show j + (i - 1) = j + i - 1 by omega, show j + (i' - 1) = j + i' - 1 by omega]
            exact h)
          unfold Nat.ModEq at this
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
          omega
      · intro i hi
        by_cases hi0 : i = 0
        · subst hi0
          simpa using hab'
        · simp only [hi0, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
          have := hg.adj (j + i - 1)
          rwa [show j + i - 1 + 1 = j + (i + 1) - 1 by omega] at this
    have := hmax _ _ hnew
    omega
  push Not at hcross
  by_cases hov : b < a
  · have hex : ∃ g, ∃ t ∈ B, ∃ s ∈ A, t < s ∧ s = t + g := ⟨a - b, b, hb, a, ha, hov, by omega⟩
    obtain ⟨t, htB, s, hsA, hts, hsg⟩ := Nat.find_spec hex
    have hmin : ∀ t' ∈ B, ∀ s' ∈ A, t' < s' → Nat.find hex ≤ s' - t' := fun t' ht' s' hs' hlt =>
      Nat.find_min' hex ⟨t', ht', s', hs', hlt, by omega⟩
    have hAgap : ∀ i ∈ A, t < i → i < s → False := fun i hi h1 h2 => by
      have := hmin t htB i hi h1; omega
    have hBgap : ∀ i ∈ B, t < i → i < s → False := fun i hi h1 h2 => by
      have := hmin i hi s hsA h2; omega
    obtain ⟨hs1, hsm, hs0⟩ := hAi s hsA
    obtain ⟨htm, htadj⟩ := hBi t htB
    have hts2 : t + 2 ≤ s := by
      by_contra h
      exact hcross t htm (by rwa [show t + 1 = s by omega]) htadj
    -- counting
    have hcount : A.card + B.card ≤ (t + 1) + (m - s + 1) := by
      have hinj : Set.InjOn (fun i => i - 1) (A : Set ℕ) := by
        intro i hi j hj h
        simp only [Finset.mem_coe] at hi hj
        have := (hAi i hi).1
        have := (hAi j hj).1
        simp only at h
        omega
      have hdisj : Disjoint (A.image (fun i => i - 1)) B := by
        rw [Finset.disjoint_left]
        intro j hj hjB
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
        obtain ⟨hi1, him, hiadj⟩ := hAi i hi
        exact hcross (i - 1) (by omega) (by rwa [show i - 1 + 1 = i by omega]) (hBi _ hjB).2
      have hsub : A.image (fun i => i - 1) ∪ B ⊆ Finset.range (t + 1) ∪ Finset.Ico (s - 1) m := by
        intro j hj
        rw [Finset.mem_union] at hj
        rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        rcases hj with hj | hj
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
          obtain ⟨hi1, him, -⟩ := hAi i hi
          by_cases h : i ≤ t
          · left; omega
          · right; have : ¬ i < s := fun h' => hAgap i hi (by omega) h'; omega
        · obtain ⟨hjm, -⟩ := hBi j hj
          by_cases h : j ≤ t
          · left; omega
          · right; have : ¬ j < s := fun h' => hBgap j hj (by omega) h'; omega
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj] at h1
      have h2 := Finset.card_union_le (Finset.range (t + 1)) (Finset.Ico (s - 1) m)
      simp only [Finset.card_range, Nat.card_Ico] at h2
      omega
    set l := seg x 0 (t + 1) ++ (seg x s (m - s + 1)).reverse with hl
    suffices h3 : l.IsChain H.Adj ∧ l.Nodup ∧ ∀ u ∈ l.getLast?, ∀ v ∈ l.head?, H.Adj u v by
      obtain ⟨u, c, hc, hlen⟩ := exists_cycle_of_list (G := H) l (by simp [hl]; omega) h3.1 h3.2.1
        h3.2.2
      exact ⟨u, c, hc, by rw [hlen]; simp [hl]; omega⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hl, List.isChain_append]
      refine ⟨isChain_seg _ _ _ fun i _ hi => hx.adj i (by omega),
        isChain_reverse_adj.2 (isChain_seg _ _ _ fun i _ hi => hx.adj i (by omega)), ?_⟩
      intro u hu v hv
      rw [getLast?_seg _ _ _ (by omega), Option.mem_def, Option.some.injEq] at hu
      rw [List.head?_reverse, getLast?_seg _ _ _ (by omega), Option.mem_def,
        Option.some.injEq] at hv
      subst hu hv
      rw [show 0 + (t + 1) - 1 = t by omega, show s + (m - s + 1) - 1 = m by omega]
      exact htadj.symm
    · rw [hl, List.nodup_append]
      refine ⟨nodup_seg _ _ _ fun i j _ hi _ hj h => hx.inj i j (by omega) (by omega) h,
        List.nodup_reverse.2 (nodup_seg _ _ _ fun i j _ hi _ hj h =>
          hx.inj i j (by omega) (by omega) h), ?_⟩
      intro u hu v hv huv
      subst huv
      obtain ⟨i, -, hi, rfl⟩ := (mem_seg _ _ _).1 hu
      obtain ⟨j, hj1, hj2, hj⟩ := (mem_seg _ _ _).1 (List.mem_reverse.1 hv)
      have := hx.inj _ _ (by omega) (by omega) hj
      omega
    · intro u hu v hv
      rw [hl, getLast?_of_append_ne (by simp [seg]), List.getLast?_reverse,
        head?_seg _ _ _ (by omega), Option.mem_def, Option.some.injEq] at hu
      rw [hl, head?_of_append_ne (by simp [seg]), head?_seg _ _ _ (by omega), Option.mem_def,
        Option.some.injEq] at hv
      subst hu hv
      exact hs0.symm
  push Not at hov
  have ha1 : 1 ≤ a := (hAi a ha).1
  have hbm : b < m := (hBi b hb).1
  have hLL := lollipop x a (fun i j hi hj h => hx.inj i j (by omega) (by omega) h)
    (fun i hi => hx.adj i (by omega)) A (fun i hi => ⟨(hAi i hi).1, hamax i hi, (hAi i hi).2.2⟩)
    ha
  have hRL : ∀ c ν, c ≤ b → b < ν → ν ≤ m → ∃ l : List W, l.head? = some (x c) ∧
      l.getLast? = some (x ν) ∧ l.IsChain H.Adj ∧ l.Nodup ∧
      (∀ y ∈ l, ∃ i, c ≤ i ∧ i ≤ m ∧ x i = y) ∧ B.card + 1 ≤ l.length := by
    intro c ν hcb hbν hνm
    have hBinj : Set.InjOn (fun i => m - i) (B : Set ℕ) := by
      intro i hi j hj h
      simp only [Finset.mem_coe] at hi hj
      have := (hBi i hi).1
      have := (hBi j hj).1
      simp only at h
      omega
    obtain ⟨l', hl'h, hl'l, hl'c, hl'n, hl'P, hl'len⟩ := lollipop (H := H) (fun i => x (m - i))
      (m - b) (fun i j hi hj h => by have := hx.inj _ _ (by omega) (by omega) h; omega)
      (fun i hi => by
        have := hx.adj (m - (i + 1)) (by omega)
        rw [show m - (i + 1) + 1 = m - i by omega] at this
        exact this.symm)
      (B.image (fun i => m - i))
      (by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
        obtain ⟨hjm, hadj⟩ := hBi j hj
        refine ⟨by omega, by have := hbmin j hj; omega, ?_⟩
        simp only [Nat.sub_zero]
        rwa [show m - (m - j) = j by omega])
      (Finset.mem_image.2 ⟨b, hb, rfl⟩) (m - ν) (by omega)
    rw [Finset.card_image_of_injOn hBinj] at hl'len
    simp only [show m - (m - ν) = ν by omega, show m - (m - b) = b by omega] at hl'h hl'l
    have hl'P' : ∀ y ∈ l', ∃ i, b ≤ i ∧ i ≤ m ∧ x i = y := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := hl'P y hy
      exact ⟨m - i, by omega, by omega, rfl⟩
    have hl'ne : l' ≠ [] := by rintro rfl; simp at hl'h
    refine ⟨seg x c (b - c) ++ l'.reverse, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (b - c) with h | h
      · have : b = c := by omega
        subst this
        rw [h]
        simp only [seg, List.range'_zero, List.map_nil, List.nil_append, List.head?_reverse]
        exact hl'l
      · rw [head?_of_append_ne (by rw [← List.length_pos_iff, length_seg]; exact h),
          head?_seg _ _ _ h]
    · rw [getLast?_of_append_ne (by simpa using hl'ne), List.getLast?_reverse]
      exact hl'h
    · rw [List.isChain_append]
      refine ⟨isChain_seg _ _ _ fun t _ ht => hx.adj t (by omega), isChain_reverse_adj.2 hl'c, ?_⟩
      intro u hu v hv
      rw [List.head?_reverse, hl'l, Option.mem_def, Option.some.injEq] at hv
      subst hv
      have h : 0 < b - c := by
        rcases Nat.eq_zero_or_pos (b - c) with h | h
        · simp [seg, h] at hu
        · exact h
      rw [getLast?_seg _ _ _ h, Option.mem_def, Option.some.injEq] at hu
      subst hu
      have := hx.adj (c + (b - c) - 1) (by omega)
      rwa [show c + (b - c) - 1 + 1 = b by omega] at this
    · rw [List.nodup_append]
      refine ⟨nodup_seg _ _ _ fun s t _ hs _ ht h => hx.inj s t (by omega) (by omega) h,
        List.nodup_reverse.2 hl'n, ?_⟩
      intro u hu v hv huv
      subst huv
      obtain ⟨s, hs1, hs2, rfl⟩ := (mem_seg _ _ _).1 hu
      obtain ⟨t, ht1, ht2, ht⟩ := hl'P' _ (List.mem_reverse.1 hv)
      have := hx.inj _ _ (by omega) (by omega) ht
      omega
    · intro y hy
      rw [List.mem_append, List.mem_reverse] at hy
      rcases hy with hy | hy
      · obtain ⟨s, hs1, hs2, rfl⟩ := (mem_seg _ _ _).1 hy
        exact ⟨s, hs1, by omega, rfl⟩
      · obtain ⟨t, ht1, ht2, rfl⟩ := hl'P' _ hy
        exact ⟨t, by omega, ht2, rfl⟩
    · simp only [List.length_append, length_seg, List.length_reverse]
      omega
  have hconn' : ∀ μ0, 0 < μ0 → μ0 < m → ∃ l : List W, l.head? = some (x 0) ∧
      l.getLast? = some (x m) ∧ l.IsChain H.Adj ∧ l.Nodup ∧ x μ0 ∉ l := by
    intro μ0 h0 hμ0
    obtain ⟨p, hp⟩ := hconn (x μ0) (x 0) (x m)
      (fun h => by have := hx.inj _ _ (by omega) (by omega) h; omega)
      (fun h => by have := hx.inj _ _ (by omega) (by omega) h; omega)
    refine ⟨p.bypass.support, ?_, ?_, p.bypass.isChain_adj_support,
      (p.bypass_isPath).support_nodup, fun h => hp (p.support_bypass_subset_support h)⟩
    · rw [← Walk.cons_tail_support]; rfl
    · rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  obtain ⟨u, c, hc, hlen⟩ := core_cycle x m a b A.card B.card hx ha1 hov hbm (by omega) hLL hRL
    hconn'
  exact ⟨u, c, hc, by omega⟩

end LongCycles
