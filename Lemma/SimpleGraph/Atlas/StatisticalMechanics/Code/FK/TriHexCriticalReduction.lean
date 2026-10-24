import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexCriticalReduction
open MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.measurableSet_twoPointEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean)
-/
@[path]
private lemma measurableSet_twoPointEvent_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {x y : V} :
-- imply
  MeasurableSet (P.twoPointEvent x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurableSet_twoPointEvent P x y

/--
[PeriodicGraph.wiredTwoPointProbability_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean)
-/
@[path]
private lemma wiredTwoPointProbability_nonneg_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {x y : V} :
-- imply
  0 ≤ P.wiredTwoPointProbability p q x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredTwoPointProbability_nonneg P p q x y

/--
[PeriodicGraph.wiredTwoPointProbability_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean)
-/
@[path]
private lemma wiredTwoPointProbability_le_one_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {x y : V} :
-- imply
  P.wiredTwoPointProbability p q x y ≤ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredTwoPointProbability_le_one P p q x y

/--
[CriticalSurfacePhaseBoundary.eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean)
-/
@[path]
private lemma eq_zero_eq
  [DecidableEq V]
  [DecidableEq W]
  {surface : ℝ → ℝ}
  {pc : ℝ}
-- given
  (hpc : pc ∈ Ioo (0 : ℝ) 1)
  (hphase : CriticalSurfacePhaseBoundary surface pc) :
-- imply
  surface pc = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.CriticalSurfacePhaseBoundary.eq_zero hpc hphase

/--
[triangularFKCriticalPolynomial_eq_zero_of_phaseBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean)
-/
@[path]
private lemma triangularFKCriticalPolynomial_eq_zero_of_phaseBoundary_eq
  [DecidableEq V]
  [DecidableEq W]
  {q pc : ℝ}
-- given
  (hpc : pc ∈ Ioo (0 : ℝ) 1)
  (hphase : TriangularCriticalPhaseBoundary q pc) :
-- imply
  triangularFKCriticalPolynomial q (fkEdgeOdds pc) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularFKCriticalPolynomial_eq_zero_of_phaseBoundary hpc hphase

/--
[hexagonalFKCriticalPolynomial_eq_zero_of_phaseBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean)
-/
@[path]
private lemma hexagonalFKCriticalPolynomial_eq_zero_of_phaseBoundary_eq
  [DecidableEq V]
  [DecidableEq W]
  {q pc : ℝ}
-- given
  (hpc : pc ∈ Ioo (0 : ℝ) 1)
  (hphase : HexagonalCriticalPhaseBoundary q pc) :
-- imply
  hexagonalFKCriticalPolynomial q (fkEdgeOdds pc) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalFKCriticalPolynomial_eq_zero_of_phaseBoundary hpc hphase

/--
[triHexCriticalPolynomials_of_dualThreshold_of_triangularPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean)
-/
@[path]
private lemma triHexCriticalPolynomials_of_dualThreshold_of_triangularPhase_eq
  [DecidableEq V]
  [DecidableEq W]
  {q pcTri pcHex : ℝ}
-- given
  (hq : 0 < q)
  (hpcTri : pcTri ∈ Ioo (0 : ℝ) 1)
  (hdual : dualParam pcTri q = pcHex)
  (hphase : TriangularCriticalPhaseBoundary q pcTri) :
-- imply
  triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0 ∧ hexagonalFKCriticalPolynomial q (fkEdgeOdds pcHex) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexCriticalPolynomials_of_dualThreshold_of_triangularPhase hq hpcTri hdual hphase

/--
[triHexCriticalPolynomials_of_dualThreshold_of_hexagonalPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean)
-/
@[path]
private lemma triHexCriticalPolynomials_of_dualThreshold_of_hexagonalPhase_eq
  [DecidableEq V]
  [DecidableEq W]
  {q pcTri pcHex : ℝ}
-- given
  (hq : 0 < q)
  (hpcTri : pcTri ∈ Ioo (0 : ℝ) 1)
  (hpcHex : pcHex ∈ Ioo (0 : ℝ) 1)
  (hdual : dualParam pcTri q = pcHex)
  (hphase : HexagonalCriticalPhaseBoundary q pcHex) :
-- imply
  triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0 ∧ hexagonalFKCriticalPolynomial q (fkEdgeOdds pcHex) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexCriticalPolynomials_of_dualThreshold_of_hexagonalPhase hq hpcTri hpcHex hdual hphase

/--
[triHexCriticalConclusion_of_exactDualThreshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean)
-/
@[path]
private lemma triHexCriticalConclusion_of_exactDualThreshold_eq
  [DecidableEq V]
  [DecidableEq W]
  {q pcTri pcHex : ℝ}
-- given
  (hq : 0 < q)
  (hpcTri : pcTri ∈ Ioo (0 : ℝ) 1)
  (hdual : dualParam pcTri q = pcHex)
  (hphase : TriangularCriticalPhaseBoundary q pcTri)
  (hdecayTri : SubcriticalTwoPointExponentialDecay triangular q pcTri)
  (hdecayTransfer : TriHexSubcriticalDecayTransfer q pcTri pcHex) :
-- imply
  (triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0 ∧ hexagonalFKCriticalPolynomial q (fkEdgeOdds pcHex) = 0) ∧ SubcriticalTwoPointExponentialDecay triangular q pcTri ∧ SubcriticalTwoPointExponentialDecay hexagonal q pcHex := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexCriticalConclusion_of_exactDualThreshold hq hpcTri hdual hphase hdecayTri hdecayTransfer

/--
[triangular_hexagonal_critical_of_phase_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean)
-/
@[path]
private lemma triangular_hexagonal_critical_of_phase_inputs_eq
  [DecidableEq V]
  [DecidableEq W]
  {q : ℝ}
-- given
  (hq : 1 ≤ q)
  (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : ℝ) 1)
  (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : ℝ) 1)
  (hsharpTri : OffCriticalSharpness (fun p => triangular.wiredPercolates p q) (triangular.criticalPoint q))
  (hsharpHex : OffCriticalSharpness (fun p => hexagonal.wiredPercolates p q) (hexagonal.criticalPoint q))
  (hcoverage : DualSubcriticalCoverage (fun p => hexagonal.wiredPercolates p q) (triangular.criticalPoint q) q)
  (hnoCoexistence : DualNoCoexistence (fun p => triangular.wiredPercolates p q) (fun p => hexagonal.wiredPercolates p q) q)
  (hphase : TriangularCriticalPhaseBoundary q (triangular.criticalPoint q))
  (hdecayTri : SubcriticalTwoPointExponentialDecay triangular q (triangular.criticalPoint q))
  (hdecayTransfer : TriHexSubcriticalDecayTransfer q (triangular.criticalPoint q) (hexagonal.criticalPoint q)) :
-- imply
  (triangularFKCriticalPolynomial q (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧ hexagonalFKCriticalPolynomial q (fkEdgeOdds (hexagonal.criticalPoint q)) = 0) ∧ SubcriticalTwoPointExponentialDecay triangular q (triangular.criticalPoint q) ∧ SubcriticalTwoPointExponentialDecay hexagonal q (hexagonal.criticalPoint q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_hexagonal_critical_of_phase_inputs hq hpcTri hpcHex hsharpTri hsharpHex hcoverage hnoCoexistence hphase hdecayTri hdecayTransfer

/--
[triangularFKCriticalPolynomial_one_of_starTriangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean)
-/
@[path]
private lemma triangularFKCriticalPolynomial_one_of_starTriangle_eq
  [DecidableEq V]
  [DecidableEq W]
  {p : ℝ}
-- given
  (hp : p ∈ Ioo (0 : ℝ) 1)
  (hstt : Universality.triProb p p p Universality.triPatABC = Universality.starProb (1 - p) (1 - p) (1 - p) Universality.starPatABC) :
-- imply
  triangularFKCriticalPolynomial 1 (fkEdgeOdds p) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularFKCriticalPolynomial_one_of_starTriangle hp hstt

/--
[triHexCriticalPolynomials_one_of_starTriangle_of_dualThreshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean)
-/
@[path]
private lemma triHexCriticalPolynomials_one_of_starTriangle_of_dualThreshold_eq
  [DecidableEq V]
  [DecidableEq W]
  {pcTri pcHex : ℝ}
-- given
  (hpcTri : pcTri ∈ Ioo (0 : ℝ) 1)
  (hdual : dualParam pcTri 1 = pcHex)
  (hstt : Universality.triProb pcTri pcTri pcTri Universality.triPatABC = Universality.starProb (1 - pcTri) (1 - pcTri) (1 - pcTri) Universality.starPatABC) :
-- imply
  triangularFKCriticalPolynomial 1 (fkEdgeOdds pcTri) = 0 ∧ hexagonalFKCriticalPolynomial 1 (fkEdgeOdds pcHex) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexCriticalPolynomials_one_of_starTriangle_of_dualThreshold hpcTri hdual hstt


-- created on 2026-10-23
