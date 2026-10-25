/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForwardSubdivision
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part4


namespace StatMech.FrontierA

open Set

open scoped BigOperators

open StatMech.Onsager.BaseCase


@[simp] theorem kwIntegralPolygonEdgePoints_length
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n) :
    (kwIntegralPolygonEdgePoints p i).length =
      (kwIntegralPolygonEdgeWord p i).length := by
  simp [kwIntegralPolygonEdgePoints]

theorem kwIntegralPolygonEdgePoints_nodup_of_axis
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n)
    (haxis : (p (i + 1) - p i).1 = 0 ∨
      (p (i + 1) - p i).2 = 0) :
    (kwIntegralPolygonEdgePoints p i).Nodup := by
  unfold kwIntegralPolygonEdgePoints kwIntegralPolygonEdgeWord
  apply (kwPrefixPositions_integralAxisWord_nodup haxis).map
  intro a b hab
  exact add_left_cancel hab

theorem kwIntegralPolygonEdgePoints_complex_mem_halfOpen
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n)
    (haxis : (p (i + 1) - p i).1 = 0 ∨
      (p (i + 1) - p i).2 = 0) {q : ℤ × ℤ}
    (hq : q ∈ kwIntegralPolygonEdgePoints p i) :
    kwIntComplex q ∈ kwRawHalfOpenEdge (fun j ↦ kwIntComplex (p j)) i := by
  rw [kwIntegralPolygonEdgePoints, List.mem_map] at hq
  obtain ⟨u, hu, rfl⟩ := hq
  obtain ⟨d, N, hword, hstep⟩ :=
    integralAxisWord_eq_replicate_of_axis haxis
  rw [kwIntegralPolygonEdgeWord, hword] at hu
  have hmem := kw_replicate_prefix_mem_halfOpen
    (kwIntComplex (p i)) d N hu
  have hend : p i + N • stepOf d = p (i + 1) := by
    rw [hstep]
    abel
  have hendC : kwIntComplex (p i) + kwIntComplex (N • stepOf d) =
      kwIntComplex (p (i + 1)) := by
    rw [← kwIntComplex_add, hend]
  rw [hendC] at hmem
  simpa only [kwRawHalfOpenEdge, kwIntComplex_add] using hmem


end StatMech.FrontierA
