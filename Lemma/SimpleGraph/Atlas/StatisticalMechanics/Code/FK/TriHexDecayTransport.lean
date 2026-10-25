import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexDecayTransport.Part2
open Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[subcriticalTwoPointExponentialDecay_of_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexDecayTransport.lean)
-/
@[path]
private lemma subcriticalTwoPointExponentialDecay_of_comparison_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V}
  {Q : PeriodicGraph W}
  {q pcP pcQ : Real}
-- given
  (hcompare : SubcriticalTwoPointComparison P Q q pcP pcQ)
  (hdecay : SubcriticalTwoPointExponentialDecay P q pcP) :
-- imply
  SubcriticalTwoPointExponentialDecay Q q pcQ := by
-- proof
  apply StatMech.FK.PeriodicPlanar.subcriticalTwoPointExponentialDecay_of_comparison hcompare hdecay

/--
[triHexGlobalTwoPointComparison_of_probabilityComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexDecayTransport.lean)
-/
@[path]
private lemma triHexGlobalTwoPointComparison_of_probabilityComparison_eq
  [DecidableEq V]
  [DecidableEq W]
  {q pcTri pcHex : Real}
-- given
  (hprob : TriHexGlobalProbabilityComparison q pcTri pcHex) :
-- imply
  TriHexGlobalTwoPointComparison q pcTri pcHex := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexGlobalTwoPointComparison_of_probabilityComparison hprob

/--
[triHexSubcriticalDecayTransfer_of_globalComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexDecayTransport.lean)
-/
@[path]
private lemma triHexSubcriticalDecayTransfer_of_globalComparison_eq
  [DecidableEq V]
  [DecidableEq W]
  {q pcTri pcHex : Real}
-- given
  (hcompare : TriHexGlobalTwoPointComparison q pcTri pcHex) :
-- imply
  TriHexSubcriticalDecayTransfer q pcTri pcHex := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexSubcriticalDecayTransfer_of_globalComparison hcompare

/--
[triHexSubcriticalDecayTransfer_of_probabilityComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexDecayTransport.lean)
-/
@[path]
private lemma triHexSubcriticalDecayTransfer_of_probabilityComparison_eq
  [DecidableEq V]
  [DecidableEq W]
  {q pcTri pcHex : Real}
-- given
  (hprob : TriHexGlobalProbabilityComparison q pcTri pcHex) :
-- imply
  TriHexSubcriticalDecayTransfer q pcTri pcHex := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexSubcriticalDecayTransfer_of_probabilityComparison hprob

/--
[triHexCriticalConclusion_of_exactDualThreshold_of_globalComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexDecayTransport.lean)
-/
@[path]
private lemma triHexCriticalConclusion_of_exactDualThreshold_of_globalComparison_eq
  [DecidableEq V]
  [DecidableEq W]
  {q pcTri pcHex : Real}
-- given
  (hq : 0 < q)
  (hpcTri : pcTri ∈ Ioo (0 : Real) 1)
  (hdual : BeffaraDC.dualParam pcTri q = pcHex)
  (hphase : TriangularCriticalPhaseBoundary q pcTri)
  (hdecayTri : SubcriticalTwoPointExponentialDecay triangular q pcTri)
  (hcompare : TriHexGlobalTwoPointComparison q pcTri pcHex) :
-- imply
  (FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds pcTri) = 0 ∧ FrontierA.hexagonalFKCriticalPolynomial q (FrontierA.fkEdgeOdds pcHex) = 0) ∧ SubcriticalTwoPointExponentialDecay triangular q pcTri ∧ SubcriticalTwoPointExponentialDecay hexagonal q pcHex := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexCriticalConclusion_of_exactDualThreshold_of_globalComparison hq hpcTri hdual hphase hdecayTri hcompare

/--
[triHexCriticalConclusion_of_exactDualThreshold_of_probabilityComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexDecayTransport.lean)
-/
@[path]
private lemma triHexCriticalConclusion_of_exactDualThreshold_of_probabilityComparison_eq
  [DecidableEq V]
  [DecidableEq W]
  {q pcTri pcHex : Real}
-- given
  (hq : 0 < q)
  (hpcTri : pcTri ∈ Ioo (0 : Real) 1)
  (hdual : BeffaraDC.dualParam pcTri q = pcHex)
  (hphase : TriangularCriticalPhaseBoundary q pcTri)
  (hdecayTri : SubcriticalTwoPointExponentialDecay triangular q pcTri)
  (hprob : TriHexGlobalProbabilityComparison q pcTri pcHex) :
-- imply
  (FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds pcTri) = 0 ∧ FrontierA.hexagonalFKCriticalPolynomial q (FrontierA.fkEdgeOdds pcHex) = 0) ∧ SubcriticalTwoPointExponentialDecay triangular q pcTri ∧ SubcriticalTwoPointExponentialDecay hexagonal q pcHex := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexCriticalConclusion_of_exactDualThreshold_of_probabilityComparison hq hpcTri hdual hphase hdecayTri hprob


-- created on 2026-10-23
