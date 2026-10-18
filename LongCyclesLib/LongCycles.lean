/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import LongCyclesLib.ErdosGallai
public import LongCyclesLib.Bondy

/-!
# Long paths, long cycles and pancyclicity

Let `G` be a finite simple graph on `n` vertices with `e(G)` edges.

* `LongCycles.erdos_gallai_path`: **Erdős–Gallai (1959).** If `G` has no path on `k` vertices
  (every path, Mathlib's `SimpleGraph.Walk.IsPath`, has length at most `k − 2`), then
  `2 e(G) ≤ (k − 2) n`.
* `LongCycles.erdos_gallai_cycle`: **Erdős–Gallai (1959).** If `k ≥ 3` and every cycle of `G`
  (Mathlib's `SimpleGraph.Walk.IsCycle`) has length less than `k`, then `2 e(G) ≤ (k − 1)(n − 1)`.
* `LongCycles.bondy`: **Bondy (1971).** If `G` is Hamiltonian, `n ≥ 3` and `n² ≤ 4 e(G)`, then
  either `G` is pancyclic (it has a cycle of every length `ℓ` with `3 ≤ ℓ ≤ n`) or `n` is even and
  `G` is isomorphic to the complete bipartite graph `K_{n/2, n/2}`.
-/

@[expose] public section

open Finset SimpleGraph

namespace LongCycles

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- **Erdős–Gallai (1959), paths.** A finite graph on `n` vertices with no path on `k` vertices
has at most `(k − 2) n / 2` edges. -/
theorem erdos_gallai_path {k : ℕ}
    (h : ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length + 2 ≤ k) :
    2 * #G.edgeFinset ≤ (k - 2) * Fintype.card V :=
  eg_path_aux G h

omit [DecidableEq V] in
/-- **Erdős–Gallai (1959), cycles.** If `k ≥ 3` and a finite graph on `n` vertices has no cycle of
length at least `k`, then it has at most `(k − 1)(n − 1) / 2` edges. -/
theorem erdos_gallai_cycle {k : ℕ} (hk : 3 ≤ k)
    (h : ∀ (u : V) (c : G.Walk u u), c.IsCycle → c.length < k) :
    2 * #G.edgeFinset ≤ (k - 1) * (Fintype.card V - 1) :=
  eg_cycle_aux G hk h

/-- **Bondy's theorem (1971).** A Hamiltonian graph on `n ≥ 3` vertices with at least `n² / 4`
edges is pancyclic, unless `n` is even and the graph is `K_{n/2, n/2}`. -/
theorem bondy (hn : 3 ≤ Fintype.card V) (hH : G.IsHamiltonian)
    (hE : Fintype.card V ^ 2 ≤ 4 * #G.edgeFinset) :
    (∀ ℓ, 3 ≤ ℓ → ℓ ≤ Fintype.card V → ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ c.length = ℓ) ∨
      (Even (Fintype.card V) ∧
        Nonempty (G ≃g completeBipartiteGraph (Fin (Fintype.card V / 2))
          (Fin (Fintype.card V / 2)))) := by
  obtain ⟨f, hf⟩ := Hamiltonicity.exists_cycArr_of_isHamiltonian hH hn
  rcases bondy_cycArr hf hE with h | h
  · left
    intro ℓ h1 h2
    obtain ⟨g, hg⟩ := h ℓ h1 h2
    obtain ⟨c, hc, hl⟩ := hg.exists_isCycle
    exact ⟨_, c, hc, hl⟩
  · exact Or.inr h

end LongCycles
