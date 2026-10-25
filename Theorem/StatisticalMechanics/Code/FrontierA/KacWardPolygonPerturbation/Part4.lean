/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericPolygonReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation.Part4


namespace StatMech.FrontierA

open scoped Convex

open Set

theorem denseRange_kwRatVertex {n : ℕ} :
    DenseRange (@kwRatVertex n) := by
  have h := DenseRange.piMap (fun _ : Fin n ↦ denseRange_kwRatComplex)
  simpa only [kwRatVertex, Pi.map_apply] using h


theorem exists_cross_stability_radius
    {n : ℕ} [NeZero n] (vertex : Fin n → ℂ)
    (hcross : ∀ i : Fin n,
      kwComplexCross (kwRawEdge vertex i) (kwRawEdge vertex (i + 1)) ≠ 0) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ v : Fin n → ℂ,
      dist v vertex < eps → ∀ i : Fin n,
        kwComplexCross (kwRawEdge v i) (kwRawEdge v (i + 1)) ≠ 0 := by
  let U : Set (Fin n → ℂ) := ⋂ i : Fin n,
    {v | kwComplexCross (kwRawEdge v i) (kwRawEdge v (i + 1)) ≠ 0}
  have hopen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    have hf : Continuous (fun v : Fin n → ℂ ↦
        kwComplexCross (kwRawEdge v i) (kwRawEdge v (i + 1))) := by
      unfold kwRawEdge kwComplexCross
      fun_prop
    exact hf.isOpen_preimage {x : ℝ | x ≠ 0} isOpen_ne
  have hvertex : vertex ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_setOf_eq]
    exact hcross
  obtain ⟨eps, heps, hball⟩ := (Metric.isOpen_iff.mp hopen) vertex hvertex
  refine ⟨eps, heps, ?_⟩
  intro v hv i
  exact Set.mem_iInter.mp (hball hv) i


end StatMech.FrontierA
