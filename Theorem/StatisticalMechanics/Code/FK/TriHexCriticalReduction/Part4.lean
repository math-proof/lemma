/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.FKTrihexDuality
import Def.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part4
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC FrontierA

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


theorem triangularFKCriticalPolynomial_eq_zero_of_phaseBoundary
    {q pc : ℝ} (hpc : pc ∈ Ioo (0 : ℝ) 1)
    (hphase : TriangularCriticalPhaseBoundary q pc) :
    triangularFKCriticalPolynomial q (fkEdgeOdds pc) = 0 := by
  exact CriticalSurfacePhaseBoundary.eq_zero
    (surface := fun p => triangularFKCriticalPolynomial q (fkEdgeOdds p))
    (pc := pc) hpc hphase

theorem hexagonalFKCriticalPolynomial_eq_zero_of_phaseBoundary
    {q pc : ℝ} (hpc : pc ∈ Ioo (0 : ℝ) 1)
    (hphase : HexagonalCriticalPhaseBoundary q pc) :
    hexagonalFKCriticalPolynomial q (fkEdgeOdds pc) = 0 := by
  exact CriticalSurfacePhaseBoundary.eq_zero
    (surface := fun p => hexagonalFKCriticalPolynomial q (fkEdgeOdds p))
    (pc := pc) hpc hphase


theorem triHexCriticalPolynomials_of_dualThreshold_of_triangularPhase
    {q pcTri pcHex : ℝ}
    (hq : 0 < q)
    (hpcTri : pcTri ∈ Ioo (0 : ℝ) 1)
    (hdual : dualParam pcTri q = pcHex)
    (hphase : TriangularCriticalPhaseBoundary q pcTri) :
    triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0 ∧
      hexagonalFKCriticalPolynomial q (fkEdgeOdds pcHex) = 0 := by
  have htri := triangularFKCriticalPolynomial_eq_zero_of_phaseBoundary
    hpcTri hphase
  have hproduct := fkEdgeOdds_mul_dualParam hpcTri.1 hpcTri.2 hq
  rw [hdual] at hproduct
  have hy : fkEdgeOdds pcTri ≠ 0 :=
    div_ne_zero (ne_of_gt hpcTri.1) (by linarith [hpcTri.2])
  exact ⟨htri,
    hexagonalFKCritical_of_dual_triangular hy hproduct htri⟩


theorem triHexCriticalPolynomials_of_dualThreshold_of_hexagonalPhase
    {q pcTri pcHex : ℝ}
    (hq : 0 < q)
    (hpcTri : pcTri ∈ Ioo (0 : ℝ) 1)
    (hpcHex : pcHex ∈ Ioo (0 : ℝ) 1)
    (hdual : dualParam pcTri q = pcHex)
    (hphase : HexagonalCriticalPhaseBoundary q pcHex) :
    triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0 ∧
      hexagonalFKCriticalPolynomial q (fkEdgeOdds pcHex) = 0 := by
  have hhex := hexagonalFKCriticalPolynomial_eq_zero_of_phaseBoundary
    hpcHex hphase
  have hproduct := fkEdgeOdds_mul_dualParam hpcTri.1 hpcTri.2 hq
  rw [hdual] at hproduct
  have hyHex : fkEdgeOdds pcHex ≠ 0 :=
    div_ne_zero (ne_of_gt hpcHex.1) (by linarith [hpcHex.2])
  exact ⟨triangularFKCritical_of_dual_hexagonal hyHex hproduct hhex,
    hhex⟩


end PeriodicPlanar
end FK
end StatMech
