/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LongCyclesLib.ErdosGallai

/-!
# Cyclic arrangements: auxiliary facts for Bondy's theorem

Building cyclic arrangements from functions on a window, counting neighbours along a cyclic
arrangement, and passing to the graph with one vertex deleted.
-/

@[expose] public section

open Finset SimpleGraph Hamiltonicity

namespace LongCycles

lemma mod_window' {L a s t : ℕ} (h : s % L = t % L) (hs1 : a ≤ s) (hs2 : s < a + L)
    (ht1 : a ≤ t) (ht2 : t < a + L) : s = t := by
  rcases le_total s t with hst | hst
  · exact mod_window h hst (by omega)
  · exact (mod_window h.symm hst (by omega)).symm

section General

variable {V : Type*} {G : SimpleGraph V}

/-- A function injective on `[0, m)` with consecutive values adjacent and `h (m - 1)` adjacent to
`h 0` gives a cyclic arrangement of length `m`. -/
lemma cycArr_of_window (h : ℕ → V) {m : ℕ} (hm : 3 ≤ m)
    (hinj : ∀ s t, s < m → t < m → h s = h t → s = t)
    (hadj : ∀ t, t + 1 < m → G.Adj (h t) (h (t + 1))) (hcl : G.Adj (h (m - 1)) (h 0)) :
    ∃ f, CycArr G m f := by
  obtain ⟨g, hg, -, -⟩ := exists_cycArr_of_list (G := G) (seg h 0 m) (by rw [length_seg]; omega)
    (isChain_seg _ _ _ (fun t _ ht => hadj t (by omega)))
    (nodup_seg _ _ _ (fun s t _ hs _ ht hst => hinj s t (by omega) (by omega) hst))
    (by
      rw [getLast?_seg _ _ _ (by omega), head?_seg _ _ _ (by omega)]
      intro a ha b hb
      rw [Option.mem_def, Option.some_inj] at ha hb
      subst ha hb
      simpa using hcl)
  rw [length_seg] at hg
  exact ⟨g, hg⟩

lemma cycArr_periodic_mul {m : ℕ} {f : ℕ → V} (hf : CycArr G m f) (j k : ℕ) :
    f (j + m * k) = f j := by
  rw [hf.eq_iff, Nat.add_mul_mod_self_left]

/-- Lifting a cyclic arrangement along an injective graph homomorphism. -/
lemma cycArr_map {W : Type*} {H : SimpleGraph W} {m : ℕ} {f : ℕ → V} (hf : CycArr G m f)
    (φ : G →g H) (hφ : Function.Injective φ) : CycArr H m (fun i => φ (f i)) where
  three_le := hf.three_le
  periodic i := by simp only [hf.periodic]
  inj i j hi hj hij := hf.inj i j hi hj (hφ hij)
  adj i := φ.map_adj (hf.adj i)

variable [Fintype V] [DecidableRel G.Adj]

/-- Counting the neighbours of `x` along a cyclic arrangement covering them. -/
lemma degree_eq_count {m : ℕ} {f : ℕ → V} (hf : CycArr G m f) (x : V)
    (hcov : ∀ w, G.Adj x w → ∃ j, f j = w) :
    G.degree x = #{p ∈ range m | G.Adj x (f p)} := by
  rw [← card_neighborFinset_eq_degree]
  symm
  refine Finset.card_bij (fun p _ => f p) ?_ ?_ ?_
  · intro p hp
    rw [mem_filter] at hp
    exact (mem_neighborFinset _ _ _).2 hp.2
  · intro a ha b hb hab
    rw [mem_filter, mem_range] at ha hb
    exact hf.inj a b ha.1 hb.1 hab
  · intro w hw
    rw [mem_neighborFinset] at hw
    obtain ⟨j, rfl⟩ := hcov w hw
    refine ⟨j % m, ?_, (hf.eq_mod j).symm⟩
    rw [mem_filter, mem_range, ← hf.eq_mod]
    exact ⟨Nat.mod_lt _ hf.pos, hw⟩

variable [DecidableEq V]

omit [DecidableRel G.Adj] [DecidableEq V] in
/-- A cyclic arrangement through all vertices is onto. -/
lemma cycArr_surj {f : ℕ → V} (hf : CycArr G (Fintype.card V) f) (w : V) : ∃ j, f j = w := by
  classical
  have hcard : #((range (Fintype.card V)).image f) = Fintype.card V := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj hij
    exact hf.inj i j (by simpa using hi) (by simpa using hj) hij
  have := eq_univ_of_card _ hcard
  have hw : w ∈ (range (Fintype.card V)).image f := this ▸ mem_univ w
  obtain ⟨j, -, hj⟩ := mem_image.1 hw
  exact ⟨j, hj⟩

omit [DecidableRel G.Adj] [DecidableEq V] in
/-- A cyclic arrangement of length `|V| - 1` misses exactly one vertex. -/
lemma cycArr_exists_missing {g : ℕ → V} (hg : CycArr G (Fintype.card V - 1) g) :
    ∃ v, (∀ j, g j ≠ v) ∧ ∀ w, w ≠ v → ∃ j, g j = w := by
  classical
  set n := Fintype.card V
  have h3 := hg.three_le
  set I := (range (n - 1)).image g with hI
  have hcard : #I = n - 1 := by
    rw [hI, card_image_of_injOn, card_range]
    intro i hi j hj hij
    exact hg.inj i j (by simpa using hi) (by simpa using hj) hij
  obtain ⟨v, -, hv⟩ := exists_mem_notMem_of_card_lt_card (s := I) (t := univ)
    (by rw [hcard, card_univ]; omega)
  have hgI : ∀ j, g j ∈ I := by
    intro j
    rw [hg.eq_mod, hI]
    exact mem_image_of_mem _ (mem_range.2 (Nat.mod_lt _ hg.pos))
  refine ⟨v, fun j hj => hv (hj ▸ hgI j), fun w hw => ?_⟩
  have hsub : I ⊆ univ.erase v := fun a ha => mem_erase.2 ⟨fun h => hv (h ▸ ha), mem_univ a⟩
  have heq := eq_of_subset_of_card_le hsub (by rw [card_erase_of_mem (mem_univ v), card_univ,
    hcard])
  have : w ∈ I := heq ▸ mem_erase.2 ⟨hw, mem_univ w⟩
  obtain ⟨j, -, hj⟩ := mem_image.1 this
  exact ⟨j, hj⟩

/-- Deleting a vertex `v` removes `deg v` edges. -/
lemma del_edges (v : V) :
    2 * #(indS G (univ.erase v)).edgeFinset + 2 * G.degree v = 2 * #G.edgeFinset := by
  rw [← sum_degrees_eq_twice_card_edges (indS G (univ.erase v)),
    ← sum_degrees_eq_twice_card_edges G]
  simp_rw [degree_indS]
  rw [Finset.sum_coe_sort (univ.erase v) (fun u => dS G (univ.erase v) u)]
  have := sum_dS_erase G univ (mem_univ v)
  simp only [dS_univ] at this
  omega

omit [DecidableRel G.Adj] in
lemma card_del (v : V) : Fintype.card (univ.erase v : Finset V) = Fintype.card V - 1 := by
  rw [Fintype.card_coe, card_erase_of_mem (mem_univ v), card_univ]

omit [Fintype V] [DecidableRel G.Adj] [DecidableEq V] in
/-- A cyclic arrangement avoiding `v` is one of the graph with `v` deleted. -/
lemma cycArr_del {S : Finset V} {m : ℕ} {g : ℕ → V} (hg : CycArr G m g) (hv : ∀ j, g j ∈ S) :
    CycArr (indS G S) m (fun j => ⟨g j, hv j⟩) where
  three_le := hg.three_le
  periodic i := by simp only [hg.periodic]
  inj i j hi hj hij := hg.inj i j hi hj (congrArg Subtype.val hij)
  adj i := by rw [comap_adj]; exact hg.adj i

omit [Fintype V] [DecidableRel G.Adj] [DecidableEq V] in
/-- A cyclic arrangement of the graph with `v` deleted is one of `G`. -/
lemma cycArr_undel {S : Finset V} {m : ℕ} {g : ℕ → S} (hg : CycArr (indS G S) m g) :
    CycArr G m (fun j => (g j).1) :=
  cycArr_map hg ⟨fun x => x.1, fun h => h⟩ Subtype.val_injective

end General

end LongCycles
