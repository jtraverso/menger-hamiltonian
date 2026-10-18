/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LongCyclesLib.ListPath

/-!
# Long cycles from a path with "non-overlapping" end neighbourhoods

The core of Dirac's long cycle lemma. Let `P = x 0, …, x m` be a path in a graph in which no single
vertex of `P` other than its ends separates `x 0` from `x m`. Suppose that from every `x μ`
(`μ < a`) there is a long path to `x a` inside `x 0, …, x a`, and from every `x c` (`c ≤ b`) a long
path to every `x ν` (`ν > b`) inside `x c, …, x m`, where `a ≤ b`. Chaining detours ("bridges")
over the vertices of `P` one obtains a cycle of length at least `KA + KB`.
-/

@[expose] public section

open SimpleGraph

namespace LongCycles

variable {W : Type*}

/-- A path given by a function: `x 0, …, x m` are distinct and consecutive ones are adjacent. -/
structure PathFn (H : SimpleGraph W) (m : ℕ) (x : ℕ → W) : Prop where
  inj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j
  adj : ∀ i, i < m → H.Adj (x i) (x (i + 1))

lemma isChain_glue {R : W → W → Prop} {A T : List W} {z : W} (hA : (A ++ [z]).IsChain R)
    (hT : T.IsChain R) (hz : T.head? = some z) : (A ++ T).IsChain R := by
  rw [List.isChain_append] at hA ⊢
  refine ⟨hA.1, hT, ?_⟩
  intro a ha b hb
  rw [hz, Option.mem_def, Option.some.injEq] at hb
  subst hb
  exact hA.2.2 a ha z (by simp)

lemma exists_first (p : W → Prop) : ∀ l : List W, (∃ y ∈ l, p y) →
    ∃ l1 z l2, l = l1 ++ z :: l2 ∧ p z ∧ ∀ y ∈ l1, ¬ p y
  | [], h => by simp at h
  | a :: l, h => by
    classical
    by_cases ha : p a
    · exact ⟨[], a, l, rfl, ha, by simp⟩
    · obtain ⟨y, hy, hpy⟩ := h
      rcases List.mem_cons.1 hy with rfl | hy
      · exact absurd hpy ha
      obtain ⟨l1, z, l2, rfl, hz, h1⟩ := exists_first p l ⟨y, hy, hpy⟩
      refine ⟨a :: l1, z, l2, rfl, hz, ?_⟩
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ha
      · exact h1 w hw

lemma head?_of_append_ne {l1 l2 : List W} (h : l1 ≠ []) : (l1 ++ l2).head? = l1.head? := by
  cases l1 with
  | nil => exact absurd rfl h
  | cons a l => rfl

lemma getLast?_of_append_ne {l1 l2 : List W} (h : l2 ≠ []) :
    (l1 ++ l2).getLast? = l2.getLast? := by
  rw [List.getLast?_append]
  cases h2 : l2.getLast? with
  | none => rw [List.getLast?_eq_none_iff] at h2; exact absurd h2 h
  | some c => rfl

variable {H : SimpleGraph W}

theorem core_cycle (x : ℕ → W) (m a b KA KB : ℕ) (hx : PathFn H m x)
    (ha1 : 1 ≤ a) (hab : a ≤ b) (hbm : b < m) (hK : 3 ≤ KA + KB)
    (hLL : ∀ μ, μ < a → ∃ l : List W, l.head? = some (x μ) ∧ l.getLast? = some (x a) ∧
        l.IsChain H.Adj ∧ l.Nodup ∧ (∀ y ∈ l, ∃ i ≤ a, x i = y) ∧ KA + 1 ≤ l.length)
    (hRL : ∀ c ν, c ≤ b → b < ν → ν ≤ m → ∃ l : List W, l.head? = some (x c) ∧
        l.getLast? = some (x ν) ∧ l.IsChain H.Adj ∧ l.Nodup ∧
        (∀ y ∈ l, ∃ i, c ≤ i ∧ i ≤ m ∧ x i = y) ∧ KB + 1 ≤ l.length)
    (hconn : ∀ μ0, 0 < μ0 → μ0 < m → ∃ l : List W, l.head? = some (x 0) ∧
        l.getLast? = some (x m) ∧ l.IsChain H.Adj ∧ l.Nodup ∧ x μ0 ∉ l) :
    ∃ (u : W) (c : H.Walk u u), c.IsCycle ∧ KA + KB ≤ c.length := by
  classical
  -- vertices on the path
  set onP : W → Prop := fun y => ∃ i ≤ m, x i = y with honP
  have hxinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j := hx.inj
  -- the invariant
  set Inv : ℕ → ℕ → Prop := fun ν c => a ≤ c ∧ c < ν ∧ ν ≤ m ∧ ∃ Y : List W,
    Y.head? = some (x ν) ∧ Y.getLast? = some (x c) ∧ Y.IsChain H.Adj ∧ Y.Nodup ∧
    (∀ y ∈ Y, ∀ i ≤ m, x i = y → i ≤ c ∨ i = ν) ∧
    ∃ W1 L W2 : List W, Y = W1 ++ L ++ W2 ∧ KA + 1 ≤ L.length ∧ ∀ y ∈ L, onP y with hInv
  set Cov : ℕ → Prop := fun μ => ∃ c ν, c ≤ μ ∧ μ < ν ∧ Inv ν c with hCov
  -- bridges
  have hbridge : ∀ μ0, a ≤ μ0 → μ0 < m → ∃ μ ν' I, μ < μ0 ∧ μ0 < ν' ∧ ν' ≤ m ∧
      (x μ :: (I ++ [x ν'])).IsChain H.Adj ∧ (x μ :: (I ++ [x ν'])).Nodup ∧
      ∀ y ∈ I, ¬ onP y := by
    intro μ0 haμ0 hμ0m
    obtain ⟨l, hlh, hll, hlc, hln, hlμ⟩ := hconn μ0 (by omega) hμ0m
    obtain ⟨u, v, I, ⟨μ, hμ, rfl⟩, ⟨ν', hν1, hν2, rfl⟩, hI, hinf⟩ :=
      exists_bridge (fun y => ∃ i < μ0, x i = y) (fun y => ∃ i, μ0 < i ∧ i ≤ m ∧ x i = y)
        (by
          rintro y ⟨i, hi, rfl⟩ ⟨j, hj1, hj2, hj⟩
          have := hxinj j i hj2 (by omega) hj
          omega)
        l ⟨x 0, hlh, 0, by omega, rfl⟩ ⟨x m, hll, m, hμ0m, le_rfl, rfl⟩
    refine ⟨μ, ν', I, hμ, hν1, hν2, hlc.infix hinf, hln.sublist hinf.sublist, ?_⟩
    rintro y hy ⟨i, him, rfl⟩
    obtain ⟨h1, h2⟩ := hI _ hy
    rcases lt_trichotomy i μ0 with h | rfl | h
    · exact h1 ⟨i, h, rfl⟩
    · exact hlμ (hinf.subset (by simp [hy]))
    · exact h2 ⟨i, h, him, rfl⟩
  -- covering
  have hcov : ∀ μ0, a ≤ μ0 → μ0 < m → Cov μ0 := by
    intro μ0
    induction μ0 using Nat.strong_induction_on with
    | _ μ0 ih =>
    intro haμ0 hμ0m
    obtain ⟨μ, ν', I, hμμ0, hμ0ν', hν'm, hQc, hQn, hIoff⟩ := hbridge μ0 haμ0 hμ0m
    have hRc : ((x ν' :: I.reverse) ++ [x μ]).IsChain H.Adj := by
      have := isChain_reverse_adj.2 hQc
      simpa using this
    have hQn' := hQn
    rw [List.nodup_cons, List.nodup_append] at hQn'
    obtain ⟨hμQ, hIn, -, hIν'⟩ := hQn'
    have hν'I : x ν' ∉ I := fun h => hIν' _ h _ (List.mem_singleton_self _) rfl
    have honPx : ∀ i ≤ m, onP (x i) := fun i hi => ⟨i, hi, rfl⟩
    have hAn : (x ν' :: I.reverse).Nodup := by
      rw [List.nodup_cons]; exact ⟨by simpa using hν'I, List.nodup_reverse.2 hIn⟩
    by_cases hμa : μ < a
    · obtain ⟨l, hlh, hll, hlc, hln, hlP, hllen⟩ := hLL μ hμa
      refine ⟨a, ν', by omega, by omega, le_rfl, by omega, hν'm, (x ν' :: I.reverse) ++ l,
        by simp, ?_, ?_, ?_, ?_, ?_⟩
      · rw [getLast?_of_append_ne (by rintro rfl; simp at hlh)]; exact hll
      · exact isChain_glue hRc hlc hlh
      · rw [List.nodup_append]
        refine ⟨hAn, hln, ?_⟩
        intro y hy z hz hyz
        subst hyz
        obtain ⟨i, hia, rfl⟩ := hlP _ hz
        simp only [List.mem_cons, List.mem_reverse] at hy
        rcases hy with h | h
        · have := hxinj _ _ (by omega) hν'm h; omega
        · exact hIoff _ h (honPx i (by omega))
      · intro y hy i him hi
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · simp only [List.mem_cons, List.mem_reverse] at hy
          rcases hy with rfl | hy
          · right; exact hxinj _ _ him hν'm hi
          · exact absurd ⟨i, him, hi⟩ (hIoff _ hy)
        · obtain ⟨j, hja, rfl⟩ := hlP _ hy
          left; have := hxinj _ _ him (by omega) hi; omega
      · refine ⟨x ν' :: I.reverse, l, [], by simp, hllen, fun y hy => ?_⟩
        obtain ⟨j, hj, rfl⟩ := hlP y hy
        exact honPx j (by omega)
    push Not at hμa
    obtain ⟨c, ν, hcμ, hμν, hac, hcν, hνm, Y, hYh, hYl, hYc, hYn, hYP, W1, L, W2, hY, hL, hLP⟩ :=
      ih μ hμμ0 hμa (by omega)
    by_cases hνμ0 : μ0 < ν
    · exact ⟨c, ν, by omega, hνμ0, hac, hcν, hνm, Y, hYh, hYl, hYc, hYn, hYP, W1, L, W2, hY, hL,
        hLP⟩
    push Not at hνμ0
    have hν'Y : x ν' ∉ Y := by
      intro h
      rcases hYP _ h ν' hν'm rfl with h | h <;> omega
    have hYne : Y ≠ [] := by rintro rfl; simp at hYh
    by_cases hdis : ∀ y ∈ I, y ∉ Y
    · set S := seg x (c + 1) (μ - c) with hS
      have hSmem : ∀ y ∈ S, ∃ t, c + 1 ≤ t ∧ t ≤ μ ∧ x t = y := by
        intro y hy
        obtain ⟨t, h1, h2, h3⟩ := (mem_seg _ _ _).1 hy
        exact ⟨t, h1, by omega, h3⟩
      set Z := Y ++ S with hZ
      have hZc : Z.IsChain H.Adj := by
        rw [List.isChain_append]
        refine ⟨hYc, isChain_seg _ _ _ fun t _ ht => hx.adj t (by omega), ?_⟩
        intro u hu v hv
        rw [hYl, Option.mem_def, Option.some.injEq] at hu
        subst hu
        have hpos : 0 < μ - c := by
          rcases Nat.eq_zero_or_pos (μ - c) with h | h
          · rw [hS, h] at hv; simp [seg] at hv
          · exact h
        rw [hS, head?_seg _ _ _ hpos, Option.mem_def, Option.some.injEq] at hv
        subst hv
        exact hx.adj c (by omega)
      have hZn : Z.Nodup := by
        rw [List.nodup_append]
        refine ⟨hYn, nodup_seg _ _ _ fun s t _ hs _ ht h => hxinj s t (by omega) (by omega) h, ?_⟩
        intro u hu v hv huv
        subst huv
        obtain ⟨t, h1, h2, rfl⟩ := hSmem _ hv
        rcases hYP _ hu t (by omega) rfl with h | h <;> omega
      have hZh : Z.head? = some (x ν) := by rw [hZ, head?_of_append_ne hYne]; exact hYh
      have hZl : Z.getLast? = some (x μ) := by
        rcases Nat.eq_zero_or_pos (μ - c) with h | h
        · have hSn : S = [] := by rw [hS, h]; simp [seg]
          rw [hZ, hSn, List.append_nil, hYl]
          congr 2; omega
        · rw [hZ, getLast?_of_append_ne (by rw [← List.length_pos_iff, hS, length_seg]; exact h),
            hS, getLast?_seg _ _ _ h]
          congr 2; omega
      refine ⟨ν, ν', hνμ0, hμ0ν', by omega, by omega, hν'm, (x ν' :: I.reverse) ++ Z.reverse,
        by simp, ?_, ?_, ?_, ?_, ?_⟩
      · rw [getLast?_of_append_ne (by simp [hZ, hYne]), List.getLast?_reverse]; exact hZh
      · exact isChain_glue hRc (isChain_reverse_adj.2 hZc) (by rw [List.head?_reverse]; exact hZl)
      · rw [List.nodup_append]
        refine ⟨hAn, List.nodup_reverse.2 hZn, ?_⟩
        intro u hu v hv huv
        subst huv
        rw [List.mem_reverse, hZ, List.mem_append] at hv
        simp only [List.mem_cons, List.mem_reverse] at hu
        rcases hu with rfl | hu
        · rcases hv with hv | hv
          · exact hν'Y hv
          · obtain ⟨t, h1, h2, h3⟩ := hSmem _ hv
            have := hxinj _ _ (by omega) hν'm h3; omega
        · rcases hv with hv | hv
          · exact hdis _ hu hv
          · obtain ⟨t, h1, h2, rfl⟩ := hSmem _ hv
            exact hIoff _ hu (honPx t (by omega))
      · intro y hy i him hi
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · simp only [List.mem_cons, List.mem_reverse] at hy
          rcases hy with rfl | hy
          · right; exact hxinj _ _ him hν'm hi
          · exact absurd ⟨i, him, hi⟩ (hIoff _ hy)
        · rw [List.mem_reverse, hZ, List.mem_append] at hy
          left
          rcases hy with hy | hy
          · rcases hYP _ hy i him hi with h | h <;> omega
          · obtain ⟨t, h1, h2, rfl⟩ := hSmem _ hy
            have := hxinj _ _ him (by omega) hi; omega
      · refine ⟨(x ν' :: I.reverse) ++ S.reverse ++ W2.reverse, L.reverse, W1.reverse, ?_,
          by simpa using hL, fun y hy => hLP y (List.mem_reverse.1 hy)⟩
        rw [hZ, hY]
        simp [List.reverse_append, List.append_assoc]
    · push Not at hdis
      obtain ⟨y0, hy0I, hy0Y⟩ := hdis
      obtain ⟨I1, z, I2, hIr, hzY, hI1⟩ :=
        exists_first (· ∈ Y) I.reverse ⟨y0, List.mem_reverse.2 hy0I, hy0Y⟩
      have hzI : z ∈ I := by rw [← List.mem_reverse, hIr]; simp
      have hzoff : ¬ onP z := hIoff z hzI
      have hI1I : ∀ y ∈ I1, y ∈ I := fun y hy => by rw [← List.mem_reverse, hIr]; simp [hy]
      -- the start of the reversed bridge, up to `z`
      have hPc : ((x ν' :: I1) ++ [z]).IsChain H.Adj := by
        refine hRc.infix ⟨[], I2 ++ [x μ], ?_⟩
        rw [hIr]; simp
      have hPn : (x ν' :: I1).Nodup := by
        refine hAn.sublist ?_
        rw [hIr]
        exact List.cons_sublist_cons.2 (List.sublist_append_left _ _)
      have hzL : z ∉ L := fun h => hzoff (hLP z h)
      have hzW : z ∈ W1 ∨ z ∈ W2 := by
        rw [hY] at hzY
        simp only [List.mem_append] at hzY
        tauto
      rcases hzW with hz1 | hz2
      · obtain ⟨W1a, W1b, rfl⟩ := List.append_of_mem hz1
        set T := z :: (W1b ++ L ++ W2) with hT
        have hYT : Y = W1a ++ T := by rw [hY, hT]; simp
        have hTsub : T <:+: Y := ⟨W1a, [], by rw [hYT]; simp⟩
        have hTne : T ≠ [] := by simp [hT]
        have hνT : x ν ∉ T := by
          intro h
          cases W1a with
          | nil =>
            rw [hYT, List.nil_append, hT] at hYh
            simp only [List.head?_cons, Option.some.injEq] at hYh
            exact hzoff ⟨ν, hνm, hYh.symm⟩
          | cons w W1a' =>
            rw [hYT] at hYh hYn
            simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hYh
            subst hYh
            rw [List.cons_append, List.nodup_cons] at hYn
            exact hYn.1 (List.mem_append_right _ h)
        refine ⟨c, ν', by omega, hμ0ν', hac, by omega, hν'm, (x ν' :: I1) ++ T,
          by simp, ?_, ?_, ?_, ?_, ?_⟩
        · rw [getLast?_of_append_ne hTne, ← getLast?_of_append_ne (l1 := W1a) hTne, ← hYT]
          exact hYl
        · exact isChain_glue hPc (hYc.infix hTsub) (by simp [hT])
        · rw [List.nodup_append]
          refine ⟨hPn, hYn.sublist hTsub.sublist, ?_⟩
          intro u hu v hv huv
          subst huv
          have hvY : u ∈ Y := hTsub.subset hv
          rcases List.mem_cons.1 hu with rfl | hu
          · exact hν'Y hvY
          · exact hI1 u hu hvY
        · intro y hy i him hi
          rw [List.mem_append] at hy
          rcases hy with hy | hy
          · rcases List.mem_cons.1 hy with rfl | hy
            · right; exact hxinj _ _ him hν'm hi
            · exact absurd ⟨i, him, hi⟩ (hIoff _ (hI1I _ hy))
          · rcases hYP _ (hTsub.subset hy) i him hi with h | h
            · left; exact h
            · subst h; exact absurd (hi ▸ hy) hνT
        · exact ⟨(x ν' :: I1) ++ z :: W1b, L, W2, by simp [hT], hL, hLP⟩
      · obtain ⟨W2a, W2b, rfl⟩ := List.append_of_mem hz2
        set T := W1 ++ L ++ W2a ++ [z] with hT
        have hYT : Y = T ++ W2b := by rw [hY, hT]; simp
        have hTsub : T <:+: Y := ⟨[], W2b, by rw [hYT]; simp⟩
        have hTne : T ≠ [] := by simp [hT]
        refine ⟨ν, ν', hνμ0, hμ0ν', by omega, by omega, hν'm, (x ν' :: I1) ++ T.reverse,
          by simp, ?_, ?_, ?_, ?_, ?_⟩
        · rw [getLast?_of_append_ne (by simpa using hTne), List.getLast?_reverse,
            ← head?_of_append_ne (l2 := W2b) hTne, ← hYT]
          exact hYh
        · exact isChain_glue hPc (isChain_reverse_adj.2 (hYc.infix hTsub))
            (by rw [List.head?_reverse, hT]; simp)
        · rw [List.nodup_append]
          refine ⟨hPn, List.nodup_reverse.2 (hYn.sublist hTsub.sublist), ?_⟩
          intro u hu v hv huv
          subst huv
          have hvY : u ∈ Y := hTsub.subset (List.mem_reverse.1 hv)
          rcases List.mem_cons.1 hu with rfl | hu
          · exact hν'Y hvY
          · exact hI1 u hu hvY
        · intro y hy i him hi
          rw [List.mem_append] at hy
          rcases hy with hy | hy
          · rcases List.mem_cons.1 hy with rfl | hy
            · right; exact hxinj _ _ him hν'm hi
            · exact absurd ⟨i, him, hi⟩ (hIoff _ (hI1I _ hy))
          · left
            rcases hYP _ (hTsub.subset (List.mem_reverse.1 hy)) i him hi with h | h <;> omega
        · refine ⟨(x ν' :: I1) ++ z :: W2a.reverse, L.reverse, W1.reverse, ?_,
            by simpa using hL, fun y hy => hLP y (List.mem_reverse.1 hy)⟩
          simp [hT, List.reverse_append, List.append_assoc]
  -- closing
  obtain ⟨c, ν, hcb, hbν, hac, hcν, hνm, Y, hYh, hYl, hYc, hYn, hYP, W1, L, W2, hY, hL, hLP⟩ :=
    hcov b hab hbm
  obtain ⟨p, hph, hpl, hpc, hpn, hpP, hplen⟩ := hRL c ν hcb hbν hνm
  have hne : x c ≠ x ν := fun h => by have := hxinj _ _ (by omega) hνm h; omega
  have hYlen : KA + 1 ≤ Y.length := by
    rw [hY]; simp only [List.length_append]; omega
  obtain ⟨u, cy, hcy, hlen⟩ := exists_cycle_of_two_paths hne p Y hpc hYc hpn hYn hph hpl hYh hYl
    (by
      intro y hyp hyY
      obtain ⟨i, hci, him, rfl⟩ := hpP y hyp
      rcases hYP _ hyY i him rfl with h | h
      · left; congr 1; omega
      · right; rw [h])
    (by omega)
  exact ⟨u, cy, hcy, by omega⟩

end LongCycles
