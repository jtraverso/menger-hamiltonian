# Menger's theorem, Hamiltonian cycles, long cycles and pancyclicity in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

## Results

This repository formalizes, for finite simple graphs:

1. **Menger's theorem (1927)** in four forms:
   - **set form:** there are an `A`–`B` separator `X` and `|X|` pairwise vertex-disjoint `A`–`B`
     paths. Together with weak duality, the maximum number of disjoint `A`–`B` paths equals the
     minimum size of an `A`–`B` separator.
   - **two-vertex form:** for non-adjacent `s ≠ t`, there are a set `X` of vertices other than
     `s` and `t` meeting every `s`–`t` walk, and `|X|` internally disjoint `s`–`t` paths.
   - **edge form:** `u` and `v` survive the deletion of any fewer than `k` edges (Mathlib's
     `IsEdgeReachable`) if and only if they are joined by `k` edge-disjoint paths.
   - **global edge form:** `G` is `k`-edge-connected (Mathlib's `IsEdgeConnected`) if and only if
     every two vertices are joined by `k` edge-disjoint paths.
2. **Bondy–Chvátal closure step (1976):** if `u`, `v` are non-adjacent and
   `deg u + deg v ≥ n`, then `G` is Hamiltonian if and only if `G + uv` is.
3. **Ore (1960):** if `n ≥ 3` and `deg u + deg v ≥ n` for all non-adjacent `u ≠ v`, then `G` is
   Hamiltonian.
4. **Dirac (1952):** if `n ≥ 3` and the minimum degree is at least `n / 2`, then `G` is
   Hamiltonian.
5. **Chvátal–Erdős (1972):** if `n ≥ 3`, `G` is `k`-connected, and every independent set has at
   most `k` vertices, then `G` is Hamiltonian.

Version 2 adds, for a graph `G` on `n` vertices with `e(G)` edges:

6. **Erdős–Gallai (1959), paths:** if `G` has no path on `k` vertices, then `2 e(G) ≤ (k − 2) n`.
7. **Erdős–Gallai (1959), cycles:** if `k ≥ 3` and every cycle has length less than `k`, then
   `2 e(G) ≤ (k − 1)(n − 1)`.
8. **Bondy (1971):** if `G` is Hamiltonian, `n ≥ 3` and `n² ≤ 4 e(G)`, then `G` is pancyclic (it
   has a cycle of every length from 3 to `n`), or `n` is even and `G ≅ K_{n/2,n/2}`.

Hamiltonicity is Mathlib's `SimpleGraph.IsHamiltonian`. Two notions are defined in the Challenge,
since Mathlib has neither:
- **separators:** `X` separates `A` from `B` when every walk from `A` to `B` passes through `X`;
- **vertex connectivity:** `G` is `k`-connected when it has more than `k` vertices and stays
  connected after deleting any fewer than `k` vertices.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements, in the namespaces `MengerTheorem`,
  `HamiltonianCycles` and (version 2) `LongPathsCycles`. It imports only Mathlib.
- [`Solution.lean`](Solution.lean), `MengerHamilton/` and (version 2) `LongCyclesLib/`: the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Menger, set form** (`MengerHamilton/MengerCore.lean`). The proof follows Diestel's induction
  on the number of edges (Diestel, *Graph Theory*, Thm 3.3.1, second proof).
  1. Delete an edge `xy`. If a separator of size `k − 1` appears, call it `Y`.
  2. Orient the edge so that `x` is reached from `A` and `y` from `B` without touching `Y`.
  3. Then `Y ∪ {x}` and `Y ∪ {y}` are separators of size `k`.
  4. Glue `k` disjoint `A`–`(Y ∪ {x})` paths with `k` disjoint `(Y ∪ {y})`–`B` paths, through
     `Y` and through the edge `xy`.
* **Two-vertex form.** Apply the set form after deleting the edges at `s` and `t`, with `A` the
  neighbours of `s` and `B` the neighbours of `t`.
* **Edge form.** Reduce to the set form in the line graph, with `A` the edges at `u` and `B` the
  edges at `v`. The converse is the pigeonhole principle.
* **Bondy–Chvátal and Ore** (`ClosureAux.lean`, `CyclicArrangement.lean`).
  - Bondy–Chvátal: a Hamiltonian cycle of `G + uv` that uses `uv` gives a Hamiltonian `u`–`v`
    path `x₁ … xₙ` of `G`. Since `deg u + deg v ≥ n`, some `i` has `u ~ x_{i+1}` and `v ~ x_i`,
    and this closes a Hamiltonian cycle of `G`.
  - Ore follows by adding missing edges one at a time until the graph is complete.
  - Dirac is the special case of Ore with every degree at least `n / 2`.
* **Chvátal–Erdős** (`ChvatalErdosAux.lean`, `LongerCycle.lean`). Take a longest cycle `C`. If a
  vertex `x` is off `C`, Menger's theorem gives `k` paths from `x` to `C` that share only `x`
  (the fan lemma). The successors on `C` of their endpoints, together with `x`, form `k + 1`
  vertices. These are not independent, and every possible edge among them yields a longer cycle.
* **Long cycles** (version 2, `LongCyclesLib/`, built on the cyclic arrangements of
  `MengerHamilton/`).
  - Dirac's lemma: a graph without a cut vertex in which every degree is at least `k/2` has a
    cycle of length at least `k`, by a longest-path argument.
  - Erdős–Gallai for cycles, by induction: delete a vertex of degree at most `(k − 1)/2`, or split
    the graph at a cut vertex; otherwise Dirac's lemma gives a long cycle.
  - Erdős–Gallai for paths: apply the cycle version to `G` plus a vertex adjacent to all others.
  - Bondy: if there is no cycle of length `n − 1`, then along a Hamiltonian cycle
    `v_i ~ v_{i+p}` forbids `v_{i+1} ~ v_{i+p+2}`, so `deg v_i + deg v_{i+1} ≤ n` and `4e ≤ n²`;
    equality forces `K_{n/2,n/2}`. Otherwise, depending on the degree of the vertex missed by an
    `(n − 1)`-cycle, either all lengths close directly or induction on `n` applies.

## Sources

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927) 96–115,
  doi:10.4064/fm-10-1-96-115.
* G. A. Dirac, *Some theorems on abstract graphs*, Proc. London Math. Soc. (3) 2 (1952) 69–81,
  doi:10.1112/plms/s3-2.1.69.
* O. Ore, *Note on Hamilton circuits*, Amer. Math. Monthly 67 (1960) 55,
  doi:10.2307/2308928.
* V. Chvátal, P. Erdős, *A note on Hamiltonian circuits*, Discrete Math. 2 (1972) 111–113,
  doi:10.1016/0012-365X(72)90079-9.
* J. A. Bondy, V. Chvátal, *A method in graph theory*, Discrete Math. 15 (1976) 111–135,
  doi:10.1016/0012-365X(76)90078-9.
* P. Erdős, T. Gallai, *On maximal paths and circuits of graphs*, Acta Math. Acad. Sci. Hungar. 10
  (1959) 337–356, doi:10.1007/BF02024498.
* J. A. Bondy, *Pancyclic graphs I*, J. Combin. Theory Ser. B 11 (1971) 80–84,
  doi:10.1016/0095-8956(71)90016-5.
* R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer (2017),
  doi:10.1007/978-3-662-53622-3.

## Authorship and use of AI

The author chose the results. The statements and proof plans were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs in three runs: Menger first, then the Hamiltonian
results using Menger, and for version 2 the long-cycle results on top of the same library. The proofs were audited and rebuilt locally. Lean checks everything
mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
