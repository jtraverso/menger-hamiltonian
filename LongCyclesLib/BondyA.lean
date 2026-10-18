/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LongCyclesLib.BondyBasic

/-!
# Bondy's theorem: graphs without a cycle of length `n - 1`

Let `f` be a Hamiltonian cyclic arrangement of `G` (on `n ≥ 4` vertices) and suppose that `G` has
no cycle of length `n - 1`. If `f i` is adjacent to `f (i + p)` then `f (i + 1)` is not adjacent to
`f (i + p + 2)`; counting gives `deg (f i) + deg (f (i + 1)) ≤ n`, hence `4 e(G) ≤ n²`, and in the
case of equality `G` is the complete bipartite graph `K_{n/2, n/2}`.
-/

@[expose] public section

open Finset SimpleGraph Hamiltonicity

namespace LongCycles

variable {V : Type*} {G : SimpleGraph V}

/-- If `f i ∼ f (i + p)` and `f (i + 1) ∼ f (i + p + 2)`, there is a cycle of length `n - 1`. -/
lemma noncross {n : ℕ} {f : ℕ → V} (hf : CycArr G n f) (hn : 4 ≤ n)
    (hno : ∀ g, ¬ CycArr G (n - 1) g) (i p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ n - 2)
    (hadj : G.Adj (f i) (f (i + p))) : ¬ G.Adj (f (i + 1)) (f (i + p + 2)) := by
  intro h'
  have hper : f (i + n) = f i := hf.periodic i
  have key : ∀ a b, i + 1 ≤ a → a < i + 1 + n → i + 1 ≤ b → b < i + 1 + n → f a = f b → a = b :=
    fun a b h1 h2 h3 h4 hab => mod_window' (hf.eq_iff.1 hab) h1 h2 h3 h4
  obtain ⟨g, hg⟩ := cycArr_of_window (G := G)
    (fun t => if t < p then f (i + 1 + t) else f (i + n + p - t)) (m := n - 1) (by omega)
    (fun s t hs ht hst => by
      split_ifs at hst <;>
        (have := key _ _ (by omega) (by omega) (by omega) (by omega) hst; omega))
    (fun t ht => by
      by_cases h1 : t + 1 < p
      · rw [ite_eq_left (by omega), ite_eq_left h1]
        have := hf.adj (i + 1 + t)
        rwa [show i + 1 + t + 1 = i + 1 + (t + 1) by omega] at this
      · by_cases h2 : t < p
        · rw [ite_eq_left h2, ite_eq_right h1, show i + n + p - (t + 1) = i + n by omega, hper,
            show i + 1 + t = i + p by omega]
          exact hadj.symm
        · rw [ite_eq_right h2, ite_eq_right h1]
          have := hf.adj (i + n + p - (t + 1))
          rw [show i + n + p - (t + 1) + 1 = i + n + p - t by omega] at this
          exact this.symm)
    (by
      rw [ite_eq_right (by omega), ite_eq_left (by omega),
        show i + n + p - (n - 1 - 1) = i + p + 2 by omega,
        show i + 1 + 0 = i + 1 by omega]
      exact h'.symm)
  exact hno g hg

variable [Fintype V] [DecidableRel G.Adj]

/-- Offsets `p < n` with `f i` adjacent to `f (i + p)`. -/
def nbrOff (G : SimpleGraph V) [DecidableRel G.Adj] (f : ℕ → V) (n i : ℕ) : Finset ℕ :=
  {p ∈ range n | G.Adj (f i) (f (i + p))}

lemma degree_eq_nbrOff {f : ℕ → V} (hf : CycArr G (Fintype.card V) f) (i : ℕ) :
    G.degree (f i) = #(nbrOff G f (Fintype.card V) i) := by
  classical
  refine degree_eq_count (hf.rotate i) (f i) (fun w _ => ?_)
  obtain ⟨j, rfl⟩ := cycArr_surj hf w
  have hpos := hf.pos
  have : i ≤ j + Fintype.card V * i := le_add_left (Nat.le_mul_of_pos_left i hpos)
  refine ⟨j + Fintype.card V * i - i, ?_⟩
  rw [show i + (j + Fintype.card V * i - i) = j + Fintype.card V * i by omega,
    cycArr_periodic_mul hf]

omit [Fintype V] in
lemma nbrOff_sub {n : ℕ} (f : ℕ → V) (i : ℕ) :
    nbrOff G f n i ⊆ Ico 1 n := by
  intro p hp
  rw [nbrOff, mem_filter, mem_range] at hp
  rw [mem_Ico]
  refine ⟨Nat.one_le_iff_ne_zero.2 fun h => ?_, hp.1⟩
  subst h
  exact G.irrefl hp.2

omit [Fintype V] in
/-- The local inequality `deg (f i) + deg (f (i + 1)) ≤ n` and its equality case. -/
lemma pair_bound {n : ℕ} {f : ℕ → V} (hf : CycArr G n f) (hn : 4 ≤ n)
    (hno : ∀ g, ¬ CycArr G (n - 1) g) (i : ℕ) :
    #(nbrOff G f n i) + #(nbrOff G f n (i + 1)) ≤ n ∧
      (#(nbrOff G f n i) + #(nbrOff G f n (i + 1)) = n → ∀ q, 2 ≤ q → q ≤ n - 1 →
        ¬ G.Adj (f (i + 1)) (f (i + 1 + q)) → G.Adj (f i) (f (i + (q - 1)))) := by
  set N0 := nbrOff G f n i with hN0
  set N1 := nbrOff G f n (i + 1) with hN1
  have hper : f (i + n) = f i := hf.periodic i
  have hlast : n - 1 ∈ N0 := by
    rw [hN0, nbrOff, mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    have := hf.adj (i + (n - 1))
    rw [show i + (n - 1) + 1 = i + n by omega, hper] at this
    exact this.symm
  have hone : 1 ∈ N1 := by
    rw [hN1, nbrOff, mem_filter, mem_range]
    exact ⟨by omega, hf.adj (i + 1)⟩
  set A := (N0.erase (n - 1)).image (· + 1) with hA
  have hAcard : #A = #N0 - 1 := by
    rw [hA, card_image_of_injective _ (add_left_injective 1), card_erase_of_mem hlast]
  have hAsub : A ⊆ Ico 1 n := by
    intro q hq
    rw [hA, mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [mem_erase] at hp
    have := mem_Ico.1 (nbrOff_sub f i hp.2)
    rw [mem_Ico]
    omega
  have hdisj : Disjoint A N1 := by
    rw [Finset.disjoint_left]
    intro q hq hq1
    rw [hA, mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [mem_erase] at hp
    have hpr := mem_Ico.1 (nbrOff_sub f i hp.2)
    have hp2 := hp.2
    rw [hN0, nbrOff, mem_filter] at hp2
    rw [hN1, nbrOff, mem_filter] at hq1
    apply noncross hf hn hno i p (by omega) (by omega) hp2.2
    rw [show i + p + 2 = i + 1 + (p + 1) by omega]
    exact hq1.2
  have hU : #(A ∪ N1) = #A + #N1 := card_union_of_disjoint hdisj
  have hUsub : A ∪ N1 ⊆ Ico 1 n := union_subset hAsub (nbrOff_sub f (i + 1))
  have hUle := card_le_card hUsub
  rw [Nat.card_Ico] at hUle
  have hN0pos : 1 ≤ #N0 := card_pos.2 ⟨_, hlast⟩
  refine ⟨by omega, fun heq q hq1 hq2 hnadj => ?_⟩
  have hUeq : A ∪ N1 = Ico 1 n :=
    eq_of_subset_of_card_le hUsub (by rw [Nat.card_Ico]; omega)
  have hq : q ∈ A ∪ N1 := hUeq ▸ mem_Ico.2 ⟨by omega, by omega⟩
  rcases mem_union.1 hq with hq | hq
  · rw [hA, mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hp2 := (mem_erase.1 hp).2
    rw [hN0, nbrOff, mem_filter] at hp2
    rw [show p + 1 - 1 = p by omega]
    exact hp2.2
  · rw [hN1, nbrOff, mem_filter] at hq
    exact absurd hq.2 hnadj

lemma sum_nbrOff {f : ℕ → V} (hf : CycArr G (Fintype.card V) f) :
    ∑ i ∈ range (Fintype.card V),
      (#(nbrOff G f (Fintype.card V) i) + #(nbrOff G f (Fintype.card V) (i + 1))) =
      4 * #G.edgeFinset := by
  classical
  simp_rw [← degree_eq_nbrOff hf]
  set n := Fintype.card V with hn
  have hinj : ∀ i ∈ range n, ∀ j ∈ range n, f i = f j → i = j :=
    fun i hi j hj hij => hf.inj i j (mem_range.1 hi) (mem_range.1 hj) hij
  have h1 : ∑ i ∈ range n, G.degree (f i) = 2 * #G.edgeFinset := by
    rw [← sum_degrees_eq_twice_card_edges]
    have himg : (range n).image f = univ :=
      eq_univ_of_card _ (by rw [card_image_of_injOn hinj, card_range])
    rw [← himg, sum_image hinj]
  have h2 : ∑ i ∈ range n, G.degree (f (i + 1)) = ∑ i ∈ range n, G.degree (f i) := by
    have a := sum_range_succ' (fun i => G.degree (f i)) n
    have b := sum_range_succ (fun i => G.degree (f i)) n
    have c : f n = f 0 := by simpa using hf.periodic 0
    rw [c] at b
    omega
  rw [sum_add_distrib, h2, h1]
  ring

omit [Fintype V] [DecidableRel G.Adj] in
lemma all_eq_of_sum (x : ℕ → ℕ) (c n : ℕ) (hle : ∀ i < n, x i ≤ c)
    (hsum : n * c ≤ ∑ i ∈ range n, x i) : ∀ i < n, x i = c := by
  intro i hi
  by_contra hne
  have : ∑ i ∈ range n, x i < ∑ i ∈ range n, c :=
    sum_lt_sum (fun j hj => hle j (mem_range.1 hj))
      ⟨i, mem_range.2 hi, lt_of_le_of_ne (hle i hi) hne⟩
  rw [sum_const, card_range, smul_eq_mul] at this
  omega

omit [Fintype V] [DecidableRel G.Adj] in
lemma shift_mod {n : ℕ} {f : ℕ → V} (hf : CycArr G n f) (i x : ℕ) :
    f (i + x) = f (i % n + x) := by
  conv_lhs => rw [← Nat.mod_add_div i n, show i % n + n * (i / n) + x = i % n + x + n * (i / n) by
    ring, cycArr_periodic_mul hf]

/-- The alternation relation in the extremal case. -/
lemma caseA_rel {f : ℕ → V} (hf : CycArr G (Fintype.card V) f) (h4 : 4 ≤ Fintype.card V)
    (hno : ∀ g, ¬ CycArr G (Fintype.card V - 1) g)
    (hE : Fintype.card V ^ 2 ≤ 4 * #G.edgeFinset) (i p : ℕ) (hp1 : 1 ≤ p)
    (hp2 : p ≤ Fintype.card V - 2) :
    G.Adj (f i) (f (i + p)) ↔ ¬ G.Adj (f (i + 1)) (f (i + 1 + (p + 1))) := by
  classical
  set n := Fintype.card V with hn
  have hpair := pair_bound hf h4 hno
  have heq := all_eq_of_sum (fun i => #(nbrOff G f n i) + #(nbrOff G f n (i + 1))) n n
    (fun i _ => (hpair i).1) (by rw [sum_nbrOff hf]; nlinarith)
  have key : ∀ i < n, (G.Adj (f i) (f (i + p)) ↔ ¬ G.Adj (f (i + 1)) (f (i + 1 + (p + 1)))) := by
    intro i hi
    constructor
    · intro h h'
      apply noncross hf h4 hno i p hp1 hp2 h
      rwa [show i + p + 2 = i + 1 + (p + 1) by omega]
    · intro h
      have := (hpair i).2 (heq i hi) (p + 1) (by omega) (by omega) h
      rwa [show p + 1 - 1 = p by omega] at this
  have hi := key (i % n) (Nat.mod_lt _ hf.pos)
  have e1 : f i = f (i % n) := hf.eq_mod i
  have e2 : f (i + p) = f (i % n + p) := shift_mod hf i p
  have e3 : f (i + 1) = f (i % n + 1) := shift_mod hf i 1
  have e4 : f (i + 1 + (p + 1)) = f (i % n + 1 + (p + 1)) := by
    rw [add_assoc, shift_mod hf i, ← add_assoc]
  rw [e1, e2, e3, e4]
  exact hi

/-- In the extremal case adjacency along the Hamiltonian cycle is given by parity. -/
lemma caseA_parity {f : ℕ → V} (hf : CycArr G (Fintype.card V) f) (h4 : 4 ≤ Fintype.card V)
    (hno : ∀ g, ¬ CycArr G (Fintype.card V - 1) g)
    (hE : Fintype.card V ^ 2 ≤ 4 * #G.edgeFinset) (u d : ℕ) (hd1 : 1 ≤ d)
    (hd2 : d ≤ Fintype.card V - 1) : G.Adj (f u) (f (u + d)) ↔ Odd d := by
  classical
  set n := Fintype.card V with hn
  have hrel := caseA_rel hf h4 hno hE
  have hpar : ∀ t, t + 1 ≤ n - 1 → ∀ i, (G.Adj (f (i + t)) (f (i + t + (t + 1))) ↔ Even t) := by
    intro t
    induction t with
    | zero => intro _ i; simpa using hf.adj i
    | succ t ih =>
      intro ht i
      have h1 := hrel (i + t) (t + 1) (by omega) (by omega)
      have h2 := ih (by omega) i
      rw [show i + (t + 1) = i + t + 1 by omega,
        show i + t + 1 + (t + 1 + 1) = i + t + 1 + (t + 1 + 1) by omega, Nat.even_add_one, ← h2,
        h1, not_not]
  have := hpar (d - 1) (by omega) (u + n - (d - 1))
  rw [show u + n - (d - 1) + (d - 1) = u + n by omega,
    show u + n + (d - 1 + 1) = u + d + n by omega, hf.periodic, hf.periodic] at this
  rw [this, Nat.even_iff, Nat.odd_iff]
  omega

lemma caseA_adj_iff {f : ℕ → V} (hf : CycArr G (Fintype.card V) f) (h4 : 4 ≤ Fintype.card V)
    (hno : ∀ g, ¬ CycArr G (Fintype.card V - 1) g)
    (hE : Fintype.card V ^ 2 ≤ 4 * #G.edgeFinset) (s t : ℕ) (hs : s < Fintype.card V)
    (ht : t < Fintype.card V) : G.Adj (f s) (f t) ↔ s % 2 ≠ t % 2 := by
  classical
  rcases lt_trichotomy s t with hst | rfl | hst
  · have := caseA_parity hf h4 hno hE s (t - s) (by omega) (by omega)
    rw [show s + (t - s) = t by omega, Nat.odd_iff] at this
    rw [this]
    omega
  · simp
  · have := caseA_parity hf h4 hno hE t (s - t) (by omega) (by omega)
    rw [show t + (s - t) = s by omega, Nat.odd_iff] at this
    rw [G.adj_comm, this]
    omega

/-- **Case A of Bondy's theorem.** -/
theorem caseA {f : ℕ → V} (hf : CycArr G (Fintype.card V) f) (h4 : 4 ≤ Fintype.card V)
    (hno : ∀ g, ¬ CycArr G (Fintype.card V - 1) g) :
    4 * #G.edgeFinset ≤ Fintype.card V ^ 2 ∧
      (Fintype.card V ^ 2 ≤ 4 * #G.edgeFinset → Even (Fintype.card V) ∧
        Nonempty (G ≃g completeBipartiteGraph (Fin (Fintype.card V / 2))
          (Fin (Fintype.card V / 2)))) := by
  classical
  set n := Fintype.card V with hn
  have hpair := pair_bound hf h4 hno
  have hsum := sum_nbrOff hf
  refine ⟨?_, fun hE => ?_⟩
  · rw [← hsum, sq]
    calc _ ≤ ∑ i ∈ range n, n := sum_le_sum (fun i _ => (hpair i).1)
      _ = n * n := by rw [sum_const, card_range, smul_eq_mul]
  have hadj := caseA_adj_iff hf h4 hno hE
  have heven : Even n := by
    have := caseA_parity hf h4 hno hE 0 (n - 1) (by omega) le_rfl
    have h' := hf.adj (n - 1)
    rw [show n - 1 + 1 = 0 + n by omega, hf.periodic, G.adj_comm] at h'
    rw [zero_add] at this
    have := this.1 h'
    rw [Nat.odd_iff] at this
    rw [Nat.even_iff]
    omega
  refine ⟨heven, ?_⟩
  set m := n / 2 with hm
  have h2m : 2 * m = n := by rw [Nat.even_iff] at heven; omega
  let idx : Fin m ⊕ Fin m → ℕ := Sum.elim (fun a => 2 * a.1) (fun a => 2 * a.1 + 1)
  have hidx : ∀ x, idx x < n := by
    rintro (a | a) <;> simp only [idx, Sum.elim_inl, Sum.elim_inr] <;> omega
  let ψ : Fin m ⊕ Fin m → V := fun x => f (idx x)
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have := hf.inj _ _ (hidx x) (hidx y) hxy
    rcases x with a | a <;> rcases y with b | b <;>
      simp only [idx, Sum.elim_inl, Sum.elim_inr] at this <;>
      first
      | (congr 1; ext; omega)
      | omega
  have hbij : Function.Bijective ψ := (Fintype.bijective_iff_injective_and_card ψ).2
    ⟨hinj, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩
  refine ⟨(⟨Equiv.ofBijective ψ hbij, fun {x y} => ?_⟩ :
    completeBipartiteGraph (Fin m) (Fin m) ≃g G).symm⟩
  change G.Adj (f (idx x)) (f (idx y)) ↔ _
  rw [hadj _ _ (hidx x) (hidx y), completeBipartiteGraph_adj]
  rcases x with a | a <;> rcases y with b | b <;>
    simp only [idx, Sum.elim_inl, Sum.elim_inr, Sum.isLeft_inl, Sum.isRight_inl,
      Sum.isLeft_inr, Sum.isRight_inr] <;> simp

end LongCycles
