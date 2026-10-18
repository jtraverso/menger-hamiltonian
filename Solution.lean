/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import MengerHamilton.Hamiltonian
public import LongCyclesLib.LongCycles

/-!
# Proofs of the statements in `Challenge.lean`

The definitions below are verbatim copies of those in `Challenge.lean`; they coincide with
`Menger.Separates` and `Hamiltonicity.IsKConnected` of `MengerHamilton/`. The theorems are proved
in `MengerHamilton/`: Menger's theorem in `Menger.lean` and `MengerCore.lean` (Diestel's induction
on the number of edges; the edge form through the line graph), the Hamiltonian results in
`Hamiltonian.lean` and its auxiliary files (the Bondy–Chvátal closure step, Ore and Dirac by
closure, Chvátal–Erdős by the fan lemma and a longest cycle). The long-cycle results (version 2)
are proved in `LongCyclesLib/` on top of `MengerHamilton/`: Dirac's long-cycle lemma by a longest
path, Erdős–Gallai for cycles by induction (deleting low-degree vertices, splitting at cut
vertices), Erdős–Gallai for paths via an apex vertex, and Bondy's theorem by counting neighbours
along a Hamiltonian cycle and induction on the number of vertices.
-/

@[expose] public section

open SimpleGraph

namespace MengerTheorem

variable {V : Type*}

/-- `X` separates `A` from `B` in `G`: every walk from a vertex of `A` to a vertex of `B` passes
through a vertex of `X`. -/
def Separates (G : SimpleGraph V) (A B X : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ x ∈ X, x ∈ p.support

/-- **Weak duality.** Pairwise vertex-disjoint `A`–`B` paths are at most as many as the vertices
of any `A`–`B` separator. -/
theorem card_le_of_separates {G : SimpleGraph V} {A B X : Finset V}
    (hX : Separates G A B X) {m : ℕ} (a b : Fin m → V) (p : ∀ i, G.Walk (a i) (b i))
    (hA : ∀ i, a i ∈ A) (hB : ∀ i, b i ∈ B)
    (hdisj : ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∉ (p j).support) :
    m ≤ X.card :=
  Menger.card_le_of_separates hX a b p hA hB hdisj

/-- **Menger's theorem (1927), set form.** In a finite graph there are an `A`–`B` separator `X`
and `|X|` pairwise vertex-disjoint paths from `A` to `B`. -/
theorem exists_separator_and_paths [Finite V] (G : SimpleGraph V)
    (A B : Finset V) :
    ∃ X : Finset V, Separates G A B X ∧
      ∃ (a b : Fin X.card → V) (p : ∀ i, G.Walk (a i) (b i)),
        (∀ i, a i ∈ A ∧ b i ∈ B ∧ (p i).IsPath) ∧
        ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∉ (p j).support :=
  Menger.exists_separator_and_paths G A B

/-- **Menger's theorem, two-vertex form.** For distinct non-adjacent vertices `s`, `t` of a finite
graph there are a set `X` of vertices other than `s` and `t` meeting every `s`–`t` walk and `|X|`
paths from `s` to `t`, any two of which share only `s` and `t`. -/
theorem exists_separator_and_paths_of_not_adj [Finite V] (G : SimpleGraph V)
    {s t : V} (hst : s ≠ t) (hadj : ¬ G.Adj s t) :
    ∃ X : Finset V, s ∉ X ∧ t ∉ X ∧ (∀ p : G.Walk s t, ∃ x ∈ X, x ∈ p.support) ∧
      ∃ p : Fin X.card → G.Walk s t, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∈ (p j).support → x = s ∨ x = t :=
  Menger.exists_separator_and_paths_of_not_adj G hst hadj

/-- **Menger's theorem, edge form.** In a finite graph, `u` and `v` remain connected after the
deletion of any fewer than `k` edges if and only if there are `k` pairwise edge-disjoint paths
from `u` to `v`. -/
theorem isEdgeReachable_iff [Finite V] (G : SimpleGraph V) (k : ℕ) (u v : V) :
    G.IsEdgeReachable k u v ↔
      ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges :=
  Menger.isEdgeReachable_iff G k u v

/-- **Menger's theorem, global edge form.** A finite graph is `k`-edge-connected if and only if any
two vertices are joined by `k` pairwise edge-disjoint paths. -/
theorem isEdgeConnected_iff [Finite V] (G : SimpleGraph V) (k : ℕ) :
    G.IsEdgeConnected k ↔
      ∀ u v : V, ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges :=
  Menger.isEdgeConnected_iff G k

end MengerTheorem

namespace HamiltonianCycles

variable {V : Type*}

/-- `G` is `k`-connected: it has more than `k` vertices and stays connected after the deletion of
any set of fewer than `k` vertices. -/
def IsKConnected [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected

/-- **Bondy–Chvátal (1976).** Adding an edge between two non-adjacent vertices whose degrees sum
to at least `n` does not change whether the graph is Hamiltonian. -/
theorem isHamiltonian_sup_edge_iff [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v) :
    (G ⊔ edge u v).IsHamiltonian ↔ G.IsHamiltonian :=
  Hamiltonicity.isHamiltonian_sup_edge_iff G huv hnadj hdeg

/-- **Ore's theorem (1960).** A graph on `n ≥ 3` vertices in which any two distinct non-adjacent
vertices have degree sum at least `n` is Hamiltonian. -/
theorem ore [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdeg : ∀ u v, u ≠ v → ¬ G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian :=
  Hamiltonicity.ore G hn hdeg

/-- **Dirac's theorem (1952).** A graph on `n ≥ 3` vertices with minimum degree at least `n / 2`
is Hamiltonian. -/
theorem dirac [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdeg : Fintype.card V ≤ 2 * G.minDegree) : G.IsHamiltonian :=
  Hamiltonicity.dirac G hn hdeg

/-- **Chvátal–Erdős (1972).** A `k`-connected graph on at least three vertices whose independent
sets have at most `k` vertices is Hamiltonian. -/
theorem chvatal_erdos [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V) (k : ℕ)
    (hk : IsKConnected G k) (hα : ∀ s : Set V, G.IsIndepSet s → s.ncard ≤ k) :
    G.IsHamiltonian :=
  Hamiltonicity.chvatal_erdos G hn k hk hα

end HamiltonianCycles

namespace LongPathsCycles

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- **Erdős–Gallai (1959), paths.** A finite graph on `n` vertices with no path on `k` vertices
has at most `(k − 2) n / 2` edges. -/
theorem erdos_gallai_path {k : ℕ}
    (h : ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length + 2 ≤ k) :
    2 * #G.edgeFinset ≤ (k - 2) * Fintype.card V :=
  LongCycles.erdos_gallai_path G h

omit [DecidableEq V] in
/-- **Erdős–Gallai (1959), cycles.** If `k ≥ 3` and a finite graph on `n` vertices has no cycle of
length at least `k`, then it has at most `(k − 1)(n − 1) / 2` edges. -/
theorem erdos_gallai_cycle {k : ℕ} (hk : 3 ≤ k)
    (h : ∀ (u : V) (c : G.Walk u u), c.IsCycle → c.length < k) :
    2 * #G.edgeFinset ≤ (k - 1) * (Fintype.card V - 1) :=
  LongCycles.erdos_gallai_cycle G hk h

/-- **Bondy's theorem (1971).** A Hamiltonian graph on `n ≥ 3` vertices with at least `n² / 4`
edges is pancyclic, unless `n` is even and the graph is `K_{n/2, n/2}`. -/
theorem bondy (hn : 3 ≤ Fintype.card V) (hH : G.IsHamiltonian)
    (hE : Fintype.card V ^ 2 ≤ 4 * #G.edgeFinset) :
    (∀ ℓ, 3 ≤ ℓ → ℓ ≤ Fintype.card V → ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ c.length = ℓ) ∨
      (Even (Fintype.card V) ∧
        Nonempty (G ≃g completeBipartiteGraph (Fin (Fintype.card V / 2))
          (Fin (Fintype.card V / 2)))) :=
  LongCycles.bondy G hn hH hE

end LongPathsCycles
