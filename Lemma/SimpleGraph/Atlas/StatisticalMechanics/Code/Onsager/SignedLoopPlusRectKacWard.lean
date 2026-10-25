import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectKacWard.Part3
open Finset SimpleGraph MeasureTheory Filter Topology StatMech StatMech.Onsager


/--
[card_ons_plusRectCutEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma card_ons_plusRectCutEven_eq
  {n : Nat}
  {config : AnchoredConfig (ons_PlusWiredVertex 2 n) none} :
-- imply
  (ons_plusRectCutEven n config).1.card = (multibondCut (ons_plusWiredBondEnds 2 n) config.1).card := by
-- proof
  apply StatMech.Onsager.card_ons_plusRectCutEven n config

/--
[ons_plusWiredContourDenominator_eq_plusRectContourSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma ons_plusWiredContourDenominator_eq_plusRectContourSum_eq
  {n : Nat}
  {beta : Real} :
-- imply
  ons_plusWiredContourDenominator 2 n beta = ons_plusRectContourSum n (Real.exp (-2 * beta)) := by
-- proof
  apply StatMech.Onsager.ons_plusWiredContourDenominator_eq_plusRectContourSum n beta

/--
[ons_plusWiredPathNumerator_eq_plusRectPathSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma ons_plusWiredPathNumerator_eq_plusRectPathSum_eq
  {n : Nat}
  {beta : Real}
  {u v : Site 2}
  {path : (hypercubicLattice 2).Walk u v} :
-- imply
  ons_plusWiredPathNumerator 2 n beta u v = ons_plusRectPathSum n path (Real.exp (-2 * beta)) := by
-- proof
  apply StatMech.Onsager.ons_plusWiredPathNumerator_eq_plusRectPathSum n beta path

/--
[ofReal_ons_plusRectContourSum_eq_kwEvenPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma ofReal_ons_plusRectContourSum_eq_kwEvenPolynomial_eq
  {n : Nat}
  {q : Real} :
-- imply
  (ons_plusRectContourSum n q : Complex) = kwEvenPolynomial (ons_rectDualGraph (2 * n + 1) (2 * n + 1)) (fun _ => (q : Complex)) := by
-- proof
  apply StatMech.Onsager.ofReal_ons_plusRectContourSum_eq_kwEvenPolynomial n q

/--
[ofReal_ons_plusRectPathSum_eq_kwEvenPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma ofReal_ons_plusRectPathSum_eq_kwEvenPolynomial_eq
  {n : Nat}
  {u v : Site 2}
  {path : (hypercubicLattice 2).Walk u v}
  {q : Real} :
-- imply
  (ons_plusRectPathSum n path q : Complex) = kwEvenPolynomial (ons_rectDualGraph (2 * n + 1) (2 * n + 1)) (ons_plusRectPathWeight n path q) := by
-- proof
  apply StatMech.Onsager.ofReal_ons_plusRectPathSum_eq_kwEvenPolynomial n path q

/--
[coe_ons_plusRectContourSum_sq_eq_kwDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma coe_ons_plusRectContourSum_sq_eq_kwDet_eq
  {n : Nat}
  {q : Real} :
-- imply
  (ons_plusRectContourSum n q : Complex) ^ 2 = ons_plusRectKWDet n q := by
-- proof
  apply StatMech.Onsager.coe_ons_plusRectContourSum_sq_eq_kwDet n q

/--
[coe_ons_plusRectPathSum_sq_eq_kwDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma coe_ons_plusRectPathSum_sq_eq_kwDet_eq
  {n : Nat}
  {u v : Site 2}
  {path : (hypercubicLattice 2).Walk u v}
  {q : Real} :
-- imply
  (ons_plusRectPathSum n path q : Complex) ^ 2 = ons_plusRectPathKWDet n path q := by
-- proof
  apply StatMech.Onsager.coe_ons_plusRectPathSum_sq_eq_kwDet n path q

/--
[ons_plusRectContourSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma ons_plusRectContourSum_pos_eq
  {n : Nat}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  0 < ons_plusRectContourSum n q := by
-- proof
  apply StatMech.Onsager.ons_plusRectContourSum_pos n q hq

/--
[coe_integral_plusMeasure_twoPoint_sq_eq_plusRectKWDet_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma coe_integral_plusMeasure_twoPoint_sq_eq_plusRectKWDet_ratio_eq
  {n : Nat}
  {beta : Real}
  {u v : Site 2}
  {path : (hypercubicLattice 2).Walk u v} :
-- imply
  ((∫ config, spin config u * spin config v ∂(plusMeasure 2 n beta 0 : Measure (ConfigSpace (Site 2)))) : Complex) ^ 2 = ons_plusRectPathKWDet n path (Real.exp (-2 * beta)) / ons_plusRectKWDet n (Real.exp (-2 * beta)) := by
-- proof
  apply StatMech.Onsager.coe_integral_plusMeasure_twoPoint_sq_eq_plusRectKWDet_ratio n beta path

/--
[norm_ons_plusRectPathWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma norm_ons_plusRectPathWeight_eq
  {n : Nat}
  {u v : Site 2}
  {path : (hypercubicLattice 2).Walk u v}
  {q : Real}
  {edge : Sym2 (ons_RectDualVertex (2 * n + 1) (2 * n + 1))}
-- given
  (hq : 0 ≤ q) :
-- imply
  ‖ons_plusRectPathWeight n path q edge‖ = q := by
-- proof
  apply StatMech.Onsager.norm_ons_plusRectPathWeight n path hq edge

/--
[ons_plusRectPathKWDet_ratio_eq_walk_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma ons_plusRectPathKWDet_ratio_eq_walk_exp_eq
  {n : Nat}
  {u v : Site 2}
  {path : (hypercubicLattice 2).Walk u v}
  {q : Real}
-- given
  (hq0 : 0 ≤ q)
  (hq : q < ons_signedLoopCriticalWeight) :
-- imply
  ons_plusRectPathKWDet n path q / ons_plusRectKWDet n q = Complex.exp (-(ons_rectDualWalkExponent (2 * n + 1) (2 * n + 1) (ons_plusRectPathWeight n path q) - ons_rectDualWalkExponent (2 * n + 1) (2 * n + 1) (fun _ ↦ (q : Complex)))) := by
-- proof
  apply StatMech.Onsager.ons_plusRectPathKWDet_ratio_eq_walk_exp n path q hq0 hq

/--
[coe_integral_plusMeasure_twoPoint_sq_eq_walk_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma coe_integral_plusMeasure_twoPoint_sq_eq_walk_exp_eq
  {n : Nat}
  {beta : Real}
  {u v : Site 2}
  {path : (hypercubicLattice 2).Walk u v}
-- given
  (hbeta : ons_betaC < beta) :
-- imply
  ((∫ config, spin config u * spin config v ∂(plusMeasure 2 n beta 0 : Measure (ConfigSpace (Site 2)))) : Complex) ^ 2 = Complex.exp (-(ons_rectDualWalkExponent (2 * n + 1) (2 * n + 1) (ons_plusRectPathWeight n path (Real.exp (-2 * beta))) - ons_rectDualWalkExponent (2 * n + 1) (2 * n + 1) (fun _ ↦ (Real.exp (-2 * beta) : Complex)))) := by
-- proof
  apply StatMech.Onsager.coe_integral_plusMeasure_twoPoint_sq_eq_walk_exp n hbeta path

/--
[ons_plusRectWalkExp_tendsto_plusState_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean)
-/
@[path]
private lemma ons_plusRectWalkExp_tendsto_plusState_sq_eq
  {beta : Real}
  {u v : Site 2}
  {path : (hypercubicLattice 2).Walk u v}
-- given
  (hbeta : ons_betaC < beta)
  (huv : u ≠ v) :
-- imply
  Tendsto (fun n ↦ Complex.exp (-(ons_rectDualWalkExponent (2 * n + 1) (2 * n + 1) (ons_plusRectPathWeight n path (Real.exp (-2 * beta))) - ons_rectDualWalkExponent (2 * n + 1) (2 * n + 1) (fun _ ↦ (Real.exp (-2 * beta) : Complex))))) atTop (nhds ((((∫ config, spin config u * spin config v ∂(plusState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.ons_plusRectWalkExp_tendsto_plusState_sq hbeta huv path


-- created on 2026-10-23
