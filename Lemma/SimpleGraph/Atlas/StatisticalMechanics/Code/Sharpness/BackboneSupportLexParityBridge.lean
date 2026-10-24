import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge
open Finset StatMech StatMech.Sharpness


/--
[shb_evenCurrentSeries_eq_cosh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shb_evenCurrentSeries_eq_cosh_eq
  {x : ℝ} :
-- imply
  shbEvenCurrentSeries x = Real.cosh x := by
-- proof
  apply StatMech.Sharpness.shb_evenCurrentSeries_eq_cosh x

/--
[shb_oddCurrentSeries_eq_sinh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shb_oddCurrentSeries_eq_sinh_eq
  {x : ℝ} :
-- imply
  shbOddCurrentSeries x = Real.sinh x := by
-- proof
  apply StatMech.Sharpness.shb_oddCurrentSeries_eq_sinh x

/--
[shb_paritySeriesMass_eq_cosh_mul_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shb_paritySeriesMass_eq_cosh_mul_polynomial_eq
  [Fintype E]
  [DecidableEq E]
  [DecidablePred P]
  {x : ℝ}
-- given
  (P : Finset E → Prop) :
-- imply
  shbParitySeriesMass P x = Real.cosh x ^ Fintype.card E * shbParityPolynomial P (Real.tanh x) := by
-- proof
  apply StatMech.Sharpness.shb_paritySeriesMass_eq_cosh_mul_polynomial P x

/--
[shb_paritySeriesMassOn_eq_cosh_mul_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shb_paritySeriesMassOn_eq_cosh_mul_polynomial_eq
  [DecidableEq E]
  {S : Finset E}
  [DecidablePred P]
  {x : ℝ}
-- given
  (P : Finset E → Prop) :
-- imply
  shbParitySeriesMassOn S P x = Real.cosh x ^ S.card * shbParityPolynomialOn S P (Real.tanh x) := by
-- proof
  apply StatMech.Sharpness.shb_paritySeriesMassOn_eq_cosh_mul_polynomial S P x

/--
[shbK4DirectFiberMass_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shbK4DirectFiberMass_cast_eq
  {E : Finset shbK4Edge}
  {t : ℚ} :
-- imply
  (shbK4DirectFiberMass E t : ℝ) = shbK4DirectFiberPolynomial E t := by
-- proof
  apply StatMech.Sharpness.shbK4DirectFiberMass_cast E t

/--
[shbK4VacuumMass_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shbK4VacuumMass_cast_eq
  {E : Finset shbK4Edge}
  {t : ℚ} :
-- imply
  (shbK4VacuumMass E t : ℝ) = shbK4VacuumPolynomial E t := by
-- proof
  apply StatMech.Sharpness.shbK4VacuumMass_cast E t

/--
[shbK4DirectRho_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shbK4DirectRho_cast_eq
  {E : Finset shbK4Edge}
  {t : ℚ} :
-- imply
  (shbK4DirectRho E t : ℝ) = shbK4DirectRhoPolynomial E t := by
-- proof
  apply StatMech.Sharpness.shbK4DirectRho_cast E t

/--
[shb_supportLex_realParity_P3_counterexample](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shb_supportLex_realParity_P3_counterexample_eq :
-- imply
  shbK4DirectRhoPolynomial shbK4H (2 / 3) < shbK4DirectRhoPolynomial shbK4G (2 / 3) := by
-- proof
  apply StatMech.Sharpness.shb_supportLex_realParity_P3_counterexample

/--
[shb_tanh_artanh_two_thirds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shb_tanh_artanh_two_thirds_eq :
-- imply
  Real.tanh (Real.artanh (2 / 3)) = (2 / 3 : ℝ) := by
-- proof
  apply StatMech.Sharpness.shb_tanh_artanh_two_thirds

/--
[shbK4DirectFiberSeriesMass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shbK4DirectFiberSeriesMass_eq_eq
  {E : Finset shbK4Edge}
  {x : ℝ} :
-- imply
  shbK4DirectFiberSeriesMass E x = Real.cosh x ^ E.card * shbK4DirectFiberPolynomial E (Real.tanh x) := by
-- proof
  apply StatMech.Sharpness.shbK4DirectFiberSeriesMass_eq E x

/--
[shbK4VacuumSeriesMass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shbK4VacuumSeriesMass_eq_eq
  {E : Finset shbK4Edge}
  {x : ℝ} :
-- imply
  shbK4VacuumSeriesMass E x = Real.cosh x ^ E.card * shbK4VacuumPolynomial E (Real.tanh x) := by
-- proof
  apply StatMech.Sharpness.shbK4VacuumSeriesMass_eq E x

/--
[shbK4DirectRhoSeries_eq_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shbK4DirectRhoSeries_eq_polynomial_eq
  {E : Finset shbK4Edge}
  {x : ℝ} :
-- imply
  shbK4DirectRhoSeries E x = shbK4DirectRhoPolynomial E (Real.tanh x) := by
-- proof
  apply StatMech.Sharpness.shbK4DirectRhoSeries_eq_polynomial E x

/--
[shb_supportLex_series_P3_counterexample](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean)
-/
@[path]
private lemma shb_supportLex_series_P3_counterexample_eq :
-- imply
  shbK4DirectRhoSeries shbK4H (Real.artanh (2 / 3)) < shbK4DirectRhoSeries shbK4G (Real.artanh (2 / 3)) := by
-- proof
  apply StatMech.Sharpness.shb_supportLex_series_P3_counterexample


-- created on 2026-10-23
