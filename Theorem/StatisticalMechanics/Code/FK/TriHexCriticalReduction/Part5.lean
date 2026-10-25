/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.FKTrihexDuality
import Def.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part5
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC FrontierA

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


theorem triHexCriticalConclusion_of_exactDualThreshold
    {q pcTri pcHex : ℝ}
    (hq : 0 < q)
    (hpcTri : pcTri ∈ Ioo (0 : ℝ) 1)
    (hdual : dualParam pcTri q = pcHex)
    (hphase : TriangularCriticalPhaseBoundary q pcTri)
    (hdecayTri : SubcriticalTwoPointExponentialDecay triangular q pcTri)
    (hdecayTransfer : TriHexSubcriticalDecayTransfer q pcTri pcHex) :
    (triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0 ∧
      hexagonalFKCriticalPolynomial q (fkEdgeOdds pcHex) = 0) ∧
      SubcriticalTwoPointExponentialDecay triangular q pcTri ∧
      SubcriticalTwoPointExponentialDecay hexagonal q pcHex := by
  exact ⟨triHexCriticalPolynomials_of_dualThreshold_of_triangularPhase
      hq hpcTri hdual hphase,
    hdecayTri, hdecayTransfer hdecayTri⟩


theorem triangular_hexagonal_critical_of_phase_inputs
    {q : ℝ}
    (hq : 1 ≤ q)
    (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : ℝ) 1)
    (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : ℝ) 1)
    (hsharpTri : OffCriticalSharpness
      (fun p => triangular.wiredPercolates p q)
      (triangular.criticalPoint q))
    (hsharpHex : OffCriticalSharpness
      (fun p => hexagonal.wiredPercolates p q)
      (hexagonal.criticalPoint q))
    (hcoverage : DualSubcriticalCoverage
      (fun p => hexagonal.wiredPercolates p q)
      (triangular.criticalPoint q) q)
    (hnoCoexistence : DualNoCoexistence
      (fun p => triangular.wiredPercolates p q)
      (fun p => hexagonal.wiredPercolates p q) q)
    (hphase : TriangularCriticalPhaseBoundary q
      (triangular.criticalPoint q))
    (hdecayTri : SubcriticalTwoPointExponentialDecay triangular q
      (triangular.criticalPoint q))
    (hdecayTransfer : TriHexSubcriticalDecayTransfer q
      (triangular.criticalPoint q) (hexagonal.criticalPoint q)) :
    (triangularFKCriticalPolynomial q
        (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧
      hexagonalFKCriticalPolynomial q
        (fkEdgeOdds (hexagonal.criticalPoint q)) = 0) ∧
      SubcriticalTwoPointExponentialDecay triangular q
        (triangular.criticalPoint q) ∧
      SubcriticalTwoPointExponentialDecay hexagonal q
        (hexagonal.criticalPoint q) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hrelation :=
    triangular.dualCritical_relation_of_sharpness_noCoexistence hexagonal
      hpcTri hpcHex hq0 hsharpTri hsharpHex hcoverage hnoCoexistence
  exact triHexCriticalConclusion_of_exactDualThreshold hq0 hpcTri
    hrelation.1 hphase hdecayTri hdecayTransfer


theorem triangularFKCriticalPolynomial_one_of_starTriangle
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hstt : Universality.triProb p p p Universality.triPatABC =
      Universality.starProb (1 - p) (1 - p) (1 - p)
        Universality.starPatABC) :
    triangularFKCriticalPolynomial 1 (fkEdgeOdds p) = 0 := by
  have hcritical : Universality.IsCriticalTri p p p :=
    (Universality.starTriangle_iff_isCriticalTri p p p).1 hstt
  have hsurface :=
    (triangularFKCriticalSurface_one_iff_isCriticalTri
      (by linarith [hp.2]) (by linarith [hp.2]) (by linarith [hp.2])).2
      hcritical
  simpa [triangularFKCriticalSurface_diagonal] using hsurface


theorem triHexCriticalPolynomials_one_of_starTriangle_of_dualThreshold
    {pcTri pcHex : ℝ}
    (hpcTri : pcTri ∈ Ioo (0 : ℝ) 1)
    (hdual : dualParam pcTri 1 = pcHex)
    (hstt : Universality.triProb pcTri pcTri pcTri Universality.triPatABC =
      Universality.starProb (1 - pcTri) (1 - pcTri) (1 - pcTri)
        Universality.starPatABC) :
    triangularFKCriticalPolynomial 1 (fkEdgeOdds pcTri) = 0 ∧
      hexagonalFKCriticalPolynomial 1 (fkEdgeOdds pcHex) = 0 := by
  have htri := triangularFKCriticalPolynomial_one_of_starTriangle hpcTri hstt
  have hproduct := fkEdgeOdds_mul_dualParam (q := (1 : ℝ))
    hpcTri.1 hpcTri.2 (by norm_num)
  rw [hdual] at hproduct
  have hy : fkEdgeOdds pcTri ≠ 0 :=
    div_ne_zero (ne_of_gt hpcTri.1) (by linarith [hpcTri.2])
  exact ⟨htri, hexagonalFKCritical_of_dual_triangular hy hproduct htri⟩

end PeriodicPlanar
end FK
end StatMech
