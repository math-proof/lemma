/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexDecayTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
import Def.StatisticalMechanics.Code.FK.TriHexDecayTransport.Part2
open Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


theorem triHexGlobalTwoPointComparison_of_probabilityComparison
    {q pcTri pcHex : Real}
    (hprob : TriHexGlobalProbabilityComparison q pcTri pcHex) :
    TriHexGlobalTwoPointComparison q pcTri pcHex := by
  intro p hp
  obtain ⟨pTri, hpTri, K, hK, hcompare⟩ := hprob p hp
  refine ⟨pTri, hpTri, K, (1 / 2 : Real), 1, hK, by norm_num,
    by norm_num, hexToTriAnchor, hcompare, ?_⟩
  intro u v
  exact half_hexagonal_dist_le_triangular_anchor_dist_add_one u v


theorem triHexSubcriticalDecayTransfer_of_globalComparison
    {q pcTri pcHex : Real}
    (hcompare : TriHexGlobalTwoPointComparison q pcTri pcHex) :
    TriHexSubcriticalDecayTransfer q pcTri pcHex := by
  intro hdecay
  exact subcriticalTwoPointExponentialDecay_of_comparison hcompare hdecay


theorem triHexSubcriticalDecayTransfer_of_probabilityComparison
    {q pcTri pcHex : Real}
    (hprob : TriHexGlobalProbabilityComparison q pcTri pcHex) :
    TriHexSubcriticalDecayTransfer q pcTri pcHex :=
  triHexSubcriticalDecayTransfer_of_globalComparison
    (triHexGlobalTwoPointComparison_of_probabilityComparison hprob)


theorem triHexCriticalConclusion_of_exactDualThreshold_of_globalComparison
    {q pcTri pcHex : Real}
    (hq : 0 < q)
    (hpcTri : pcTri ∈ Ioo (0 : Real) 1)
    (hdual : BeffaraDC.dualParam pcTri q = pcHex)
    (hphase : TriangularCriticalPhaseBoundary q pcTri)
    (hdecayTri : SubcriticalTwoPointExponentialDecay triangular q pcTri)
    (hcompare : TriHexGlobalTwoPointComparison q pcTri pcHex) :
    (FrontierA.triangularFKCriticalPolynomial q
          (FrontierA.fkEdgeOdds pcTri) = 0 ∧
        FrontierA.hexagonalFKCriticalPolynomial q
          (FrontierA.fkEdgeOdds pcHex) = 0) ∧
      SubcriticalTwoPointExponentialDecay triangular q pcTri ∧
      SubcriticalTwoPointExponentialDecay hexagonal q pcHex := by
  exact triHexCriticalConclusion_of_exactDualThreshold hq hpcTri hdual
    hphase hdecayTri
    (triHexSubcriticalDecayTransfer_of_globalComparison hcompare)


theorem triHexCriticalConclusion_of_exactDualThreshold_of_probabilityComparison
    {q pcTri pcHex : Real}
    (hq : 0 < q)
    (hpcTri : pcTri ∈ Ioo (0 : Real) 1)
    (hdual : BeffaraDC.dualParam pcTri q = pcHex)
    (hphase : TriangularCriticalPhaseBoundary q pcTri)
    (hdecayTri : SubcriticalTwoPointExponentialDecay triangular q pcTri)
    (hprob : TriHexGlobalProbabilityComparison q pcTri pcHex) :
    (FrontierA.triangularFKCriticalPolynomial q
          (FrontierA.fkEdgeOdds pcTri) = 0 ∧
        FrontierA.hexagonalFKCriticalPolynomial q
          (FrontierA.fkEdgeOdds pcHex) = 0) ∧
      SubcriticalTwoPointExponentialDecay triangular q pcTri ∧
      SubcriticalTwoPointExponentialDecay hexagonal q pcHex := by
  exact triHexCriticalConclusion_of_exactDualThreshold hq hpcTri hdual
    hphase hdecayTri
    (triHexSubcriticalDecayTransfer_of_probabilityComparison hprob)

end PeriodicPlanar
end FK
end StatMech
