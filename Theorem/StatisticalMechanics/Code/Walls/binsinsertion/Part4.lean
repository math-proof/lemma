/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcl2close.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcorcorridors.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Def.StatisticalMechanics.Code.Walls.binsinsertion.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bins_iEqTop_subset_iUnion_NineMeetBox :
    {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤}
      ⊆ ⋃ n, bins_NineMeetBox n := by
  intro ω htop
  have hInf : (infiniteClusters 2 ω).Infinite :=
    Set.encard_eq_top_iff.mp htop
  let emb : ℕ ↪ (infiniteClusters 2 ω) :=
    @Infinite.natEmbedding (infiniteClusters 2 ω) (Set.Infinite.to_subtype hInf)
  let C : Fin 9 → Set (Site 2) := fun i ↦ (emb i.val).1
  have hCmem (i : Fin 9) : C i ∈ infiniteClusters 2 ω := (emb i.val).2
  have hC (i : Fin 9) : (C i).Infinite ∧ ∃ x, C i = cluster 2 ω x := by
    simpa [infiniteClusters] using hCmem i
  let x : Fin 9 → Site 2 := fun i ↦ Classical.choose (hC i).2
  have hxC (i : Fin 9) : C i = cluster 2 ω (x i) := Classical.choose_spec (hC i).2
  obtain ⟨n, hn⟩ := Lattice.finite_subset_box (Set.range x) (Set.finite_range x)
  refine Set.mem_iUnion.mpr ⟨n, htop, x, ?_, ?_⟩
  · intro i
    refine ⟨hn ⟨i, rfl⟩, ?_⟩
    rw [← hxC i]
    exact (hC i).1
  · intro i j hij heq
    have hCeq : C i = C j := by rw [hxC i, hxC j, heq]
    have hemb : emb i.val = emb j.val := Subtype.ext hCeq
    have hijval : i.val = j.val := emb.injective hemb
    exact hij (Fin.ext hijval)


theorem bins_exists_NineMeetBox_pos (p : ℝ≥0) (hp1 : p ≤ 1)
    (htop : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω | numInfiniteClusters 2 ω = ⊤}) :
    ∃ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (bins_NineMeetBox n) := by
  let μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hu : μ (⋃ n, bins_NineMeetBox n) = 0 := measure_iUnion_null hcon
  have hz : μ {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} = 0 :=
    le_antisymm ((measure_mono bins_iEqTop_subset_iUnion_NineMeetBox).trans_eq hu) bot_le
  apply (ne_of_gt htop)
  simpa [μ] using hz


end StatMech.Walls
