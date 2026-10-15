/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Menger's theorem and sufficient conditions for Hamiltonian cycles

For a finite simple graph `G`:

* `MengerTheorem.card_le_of_separates`: if `X` separates `A` from `B` (every walk from `A` to
  `B` meets `X`), any family of pairwise vertex-disjoint `A`–`B` paths has at most `|X|`
  members.
* `MengerTheorem.exists_separator_and_paths`: **Menger (1927), set form.** There are an
  `A`–`B` separator `X` and `|X|` pairwise vertex-disjoint `A`–`B` paths; so the maximum number
  of disjoint `A`–`B` paths equals the minimum size of an `A`–`B` separator.
* `MengerTheorem.exists_separator_and_paths_of_not_adj`: **two-vertex form.** For distinct
  non-adjacent `s`, `t` there are a set `X` of vertices other than `s`, `t` meeting every
  `s`–`t` walk and `|X|` `s`–`t` paths, any two of which share only `s` and `t`.
* `MengerTheorem.isEdgeReachable_iff`: **edge form.** `u` and `v` stay connected after deleting
  fewer than `k` edges (Mathlib's `IsEdgeReachable`) if and only if there are `k` pairwise
  edge-disjoint `u`–`v` paths.
* `MengerTheorem.isEdgeConnected_iff`: **global edge form.** `G` is
  `k`-edge-connected (Mathlib's `IsEdgeConnected`) if and only if any two vertices are joined by
  `k` pairwise edge-disjoint paths.
* `HamiltonianCycles.isHamiltonian_sup_edge_iff`: **Bondy–Chvátal (1976).** If `u`, `v` are
  distinct non-adjacent vertices with `deg u + deg v ≥ n`, then `G` is Hamiltonian if and only if
  `G + uv` is.
* `HamiltonianCycles.ore`: **Ore (1960).** If `n ≥ 3` and `deg u + deg v ≥ n` for all distinct
  non-adjacent `u`, `v`, then `G` is Hamiltonian.
* `HamiltonianCycles.dirac`: **Dirac (1952).** If `n ≥ 3` and every degree is at least `n / 2`,
  then `G` is Hamiltonian.
* `HamiltonianCycles.chvatal_erdos`: **Chvátal–Erdős (1972).** If `n ≥ 3`, `G` is
  `k`-connected and every independent set has at most `k` vertices, then `G` is Hamiltonian.

`X` separates `A` from `B` (`MengerTheorem.Separates`) when every walk from `A` to `B` passes
through `X`. `G` is `k`-connected (`HamiltonianCycles.IsKConnected`) when it has more than `k`
vertices and stays connected after the deletion of any set of fewer than `k` vertices.
Hamiltonicity, `k`-edge-reachability and `k`-edge-connectivity are Mathlib's
`SimpleGraph.IsHamiltonian`, `SimpleGraph.IsEdgeReachable` and `SimpleGraph.IsEdgeConnected`.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
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
    m ≤ X.card := by
  sorry

/-- **Menger's theorem (1927), set form.** In a finite graph there are an `A`–`B` separator `X`
and `|X|` pairwise vertex-disjoint paths from `A` to `B`. -/
theorem exists_separator_and_paths [Finite V] (G : SimpleGraph V)
    (A B : Finset V) :
    ∃ X : Finset V, Separates G A B X ∧
      ∃ (a b : Fin X.card → V) (p : ∀ i, G.Walk (a i) (b i)),
        (∀ i, a i ∈ A ∧ b i ∈ B ∧ (p i).IsPath) ∧
        ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∉ (p j).support := by
  sorry

/-- **Menger's theorem, two-vertex form.** For distinct non-adjacent vertices `s`, `t` of a finite
graph there are a set `X` of vertices other than `s` and `t` meeting every `s`–`t` walk and `|X|`
paths from `s` to `t`, any two of which share only `s` and `t`. -/
theorem exists_separator_and_paths_of_not_adj [Finite V] (G : SimpleGraph V)
    {s t : V} (hst : s ≠ t) (hadj : ¬ G.Adj s t) :
    ∃ X : Finset V, s ∉ X ∧ t ∉ X ∧ (∀ p : G.Walk s t, ∃ x ∈ X, x ∈ p.support) ∧
      ∃ p : Fin X.card → G.Walk s t, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∈ (p j).support → x = s ∨ x = t := by
  sorry

/-- **Menger's theorem, edge form.** In a finite graph, `u` and `v` remain connected after the
deletion of any fewer than `k` edges if and only if there are `k` pairwise edge-disjoint paths
from `u` to `v`. -/
theorem isEdgeReachable_iff [Finite V] (G : SimpleGraph V) (k : ℕ) (u v : V) :
    G.IsEdgeReachable k u v ↔
      ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges := by
  sorry

/-- **Menger's theorem, global edge form.** A finite graph is `k`-edge-connected if and only if any
two vertices are joined by `k` pairwise edge-disjoint paths. -/
theorem isEdgeConnected_iff [Finite V] (G : SimpleGraph V) (k : ℕ) :
    G.IsEdgeConnected k ↔
      ∀ u v : V, ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges := by
  sorry

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
    (G ⊔ edge u v).IsHamiltonian ↔ G.IsHamiltonian := by
  sorry

/-- **Ore's theorem (1960).** A graph on `n ≥ 3` vertices in which any two distinct non-adjacent
vertices have degree sum at least `n` is Hamiltonian. -/
theorem ore [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdeg : ∀ u v, u ≠ v → ¬ G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by
  sorry

/-- **Dirac's theorem (1952).** A graph on `n ≥ 3` vertices with minimum degree at least `n / 2`
is Hamiltonian. -/
theorem dirac [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdeg : Fintype.card V ≤ 2 * G.minDegree) : G.IsHamiltonian := by
  sorry

/-- **Chvátal–Erdős (1972).** A `k`-connected graph on at least three vertices whose independent
sets have at most `k` vertices is Hamiltonian. -/
theorem chvatal_erdos [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V) (k : ℕ)
    (hk : IsKConnected G k) (hα : ∀ s : Set V, G.IsIndepSet s → s.ncard ≤ k) :
    G.IsHamiltonian := by
  sorry

end HamiltonianCycles
