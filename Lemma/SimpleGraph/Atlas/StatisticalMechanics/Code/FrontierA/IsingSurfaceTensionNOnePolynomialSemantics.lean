import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics.Part5
open Finset Std StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[BiPoly.eval_ofTerms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_ofTerms_eq
  {X Y : Real}
  {ts : List BiTerm} :
-- imply
  BiPoly.eval X Y (BiPoly.ofTerms ts) = (ts.map (BiTerm.eval X Y)).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_ofTerms X Y ts

/--
[BiPoly.eval_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_monomial_eq
  {X Y : Real}
  {ex ey coeff : Int} :
-- imply
  BiPoly.eval X Y (.monomial ex ey coeff) = (coeff : Real) * X ^ ex * Y ^ ey := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_monomial X Y ex ey coeff

/--
[BiPoly.eval_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_add_eq
  {X Y : Real}
  {p q : BiPoly} :
-- imply
  BiPoly.eval X Y (p + q) = p.eval X Y + q.eval X Y := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_add X Y p q

/--
[BiPoly.eval_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_neg_eq
  {X Y : Real}
  {p : BiPoly} :
-- imply
  BiPoly.eval X Y (-p) = -p.eval X Y := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_neg X Y p

/--
[BiPoly.eval_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_sub_eq
  {X Y : Real}
  {p q : BiPoly} :
-- imply
  BiPoly.eval X Y (p - q) = p.eval X Y - q.eval X Y := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_sub X Y p q

/--
[BiPoly.eval_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_mul_eq
  {X Y : Real}
  {p q : BiPoly}
-- given
  (hX : X ≠ 0)
  (hY : Y ≠ 0) :
-- imply
  BiPoly.eval X Y (p * q) = p.eval X Y * q.eval X Y := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_mul X Y hX hY p q

/--
[BiPoly.eval_mapExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_mapExponent_eq
  {X Y : Real}
  {p : BiPoly}
-- given
  (f : Int -> Int -> Int × Int) :
-- imply
  (p.mapExponent f).eval X Y = (p.terms.map fun t => (t.coeff : Real) * X ^ (f t.ex t.ey).1 * Y ^ (f t.ex t.ey).2).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_mapExponent X Y f p

/--
[BiPoly.eval_flipY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_flipY_eq
  {X Y : Real}
  {p : BiPoly} :
-- imply
  (p.mapExponent fun ex ey => (ex, -ey)).eval X Y = p.eval X Y⁻¹ := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_flipY X Y p

/--
[BiPoly.eval_scaleObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_scaleObservable_eq
  {X Y : Real}
  {p : BiPoly}
  {power : Nat} :
-- imply
  (p.scaleObservable power).eval X Y = (p.terms.map fun t => ((t.coeff * (2 * t.ey - 9) ^ power : Int) : Real) * X ^ t.ex * Y ^ t.ey).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_scaleObservable X Y p power

/--
[BiPoly.eval_divYsqSubOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_divYsqSubOne_eq
  {X Y : Real}
  {top : Nat}
  {p : BiPoly}
-- given
  (hX : X ≠ 0)
  (hY : Y ≠ 0) :
-- imply
  p.eval X Y = (p.divYsqSubOne top).1.eval X Y * (Y ^ 2 - 1) + (p.divYsqSubOne top).2.eval X Y := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_divYsqSubOne X Y hX hY top p

/--
[BiPoly.eval_divXsqSubOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_divXsqSubOne_eq
  {X Y : Real}
  {top : Nat}
  {p : BiPoly}
-- given
  (hX : X ≠ 0)
  (hY : Y ≠ 0) :
-- imply
  p.eval X Y = (p.divXsqSubOne top).1.eval X Y * (X ^ 2 - 1) + (p.divXsqSubOne top).2.eval X Y := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_divXsqSubOne X Y hX hY top p

/--
[BiPoly.eval_eq_zero_of_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_eq_zero_of_isEmpty_eq
  {X Y : Real}
  {p : BiPoly}
-- given
  (h : p.terms.isEmpty = true) :
-- imply
  p.eval X Y = 0 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_eq_zero_of_isEmpty X Y p h

/--
[eval_clearedSkewPolyOf_eq_factors_of_remainderCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_clearedSkewPolyOf_eq_factors_of_remainderCertificate_eq
  {p : BiPoly}
  {X Y : Real}
-- given
  (hX : X ≠ 0)
  (hY : Y ≠ 0)
  (hcert : remainderCertificateOf p = true) :
-- imply
  (clearedSkewPolyOf p).eval X Y = (quotientPolyOf p).eval X Y * (X ^ 2 - 1) * (Y ^ 2 - 1) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.eval_clearedSkewPolyOf_eq_factors_of_remainderCertificate p X Y hX hY hcert

/--
[BiPoly.eval_shiftToOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_shiftToOne_eq
  {q : BiPoly}
  {C D : Real}
-- given
  (hexp : ∀ t ∈ q.terms, 0 ≤ t.ex ∧ 0 ≤ t.ey) :
-- imply
  q.shiftToOne.eval C D = q.eval (1 + C) (1 + D) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_shiftToOne q C D hexp

/--
[BiPoly.eval_shiftedQuotientPolyOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_shiftedQuotientPolyOf_eq
  {p : BiPoly}
  {C D : Real}
-- given
  (hexp : ∀ t ∈ (quotientPolyOf p).terms, 0 ≤ t.ex ∧ 0 ≤ t.ey) :
-- imply
  (shiftedQuotientPolyOf p).eval C D = (quotientPolyOf p).eval (1 + C) (1 + D) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_shiftedQuotientPolyOf p C D hexp

/--
[BiPoly.eval_nonneg_of_coeff_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_nonneg_of_coeff_nonneg_eq
  {p : BiPoly}
  {X Y : Real}
-- given
  (hX : 0 ≤ X)
  (hY : 0 ≤ Y)
  (hcoeff : ∀ t ∈ p.terms, 0 ≤ t.coeff) :
-- imply
  0 ≤ p.eval X Y := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_nonneg_of_coeff_nonneg p X Y hX hY hcoeff

/--
[eval_shiftedQuotientPolyOf_nonneg_of_coefficientCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_shiftedQuotientPolyOf_nonneg_of_coefficientCertificate_eq
  {p : BiPoly}
  {C D : Real}
-- given
  (hC : 0 ≤ C)
  (hD : 0 ≤ D)
  (hcert : coefficientCertificateOf p = true) :
-- imply
  0 ≤ (shiftedQuotientPolyOf p).eval C D := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.eval_shiftedQuotientPolyOf_nonneg_of_coefficientCertificate p C D hC hD hcert

/--
[eval_quotientPolyOf_nonneg_of_coefficientCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_quotientPolyOf_nonneg_of_coefficientCertificate_eq
  {p : BiPoly}
  {X Y : Real}
-- given
  (hX : 1 ≤ X)
  (hY : 1 ≤ Y)
  (hexp : ∀ t ∈ (quotientPolyOf p).terms, 0 ≤ t.ex ∧ 0 ≤ t.ey)
  (hcert : coefficientCertificateOf p = true) :
-- imply
  0 ≤ (quotientPolyOf p).eval X Y := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.eval_quotientPolyOf_nonneg_of_coefficientCertificate p X Y hX hY hexp hcert

/--
[BiPoly.eval_mapExponent_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_mapExponent_add_eq
  {p : BiPoly}
  {X Y : Real}
  {ax ay : Int}
-- given
  (hX : X ≠ 0)
  (hY : Y ≠ 0) :
-- imply
  (p.mapExponent fun ex ey => (ex + ax, ey + ay)).eval X Y = p.eval X Y * X ^ ax * Y ^ ay := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_mapExponent_add p X Y hX hY ax ay

/--
[eval_clearedSkewPolyOf_eq_scaled_neg_skew](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_clearedSkewPolyOf_eq_scaled_neg_skew_eq
  {p : BiPoly}
  {X Y : Real}
-- given
  (hX : X ≠ 0)
  (hY : Y ≠ 0) :
-- imply
  (clearedSkewPolyOf p).eval X Y = -(reflectedVarianceSkewPolyOf p).eval X Y * X ^ (-17 : Int) * Y ^ (17 : Int) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.eval_clearedSkewPolyOf_eq_scaled_neg_skew p X Y hX hY

/--
[eval_clearedSkewPolyOf_nonneg_of_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_clearedSkewPolyOf_nonneg_of_certificate_eq
  {p : BiPoly}
  {X Y : Real}
-- given
  (hX : 1 ≤ X)
  (hY : 1 ≤ Y)
  (hexp : ∀ t ∈ (quotientPolyOf p).terms, 0 ≤ t.ex ∧ 0 ≤ t.ey)
  (hcert : certificateOf p = true) :
-- imply
  0 ≤ (clearedSkewPolyOf p).eval X Y := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.eval_clearedSkewPolyOf_nonneg_of_certificate p X Y hX hY hexp hcert

/--
[eval_reflectedVarianceSkewPolyOf_nonpos_of_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_reflectedVarianceSkewPolyOf_nonpos_of_certificate_eq
  {p : BiPoly}
  {X Y : Real}
-- given
  (hX : 1 ≤ X)
  (hY : 1 ≤ Y)
  (hexp : ∀ t ∈ (quotientPolyOf p).terms, 0 ≤ t.ex ∧ 0 ≤ t.ey)
  (hcert : certificateOf p = true) :
-- imply
  (reflectedVarianceSkewPolyOf p).eval X Y ≤ 0 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.eval_reflectedVarianceSkewPolyOf_nonpos_of_certificate p X Y hX hY hexp hcert

/--
[eval_reflectedVarianceSkewPolyOf_nonpos_of_explicit_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean)
-/
@[path]
private lemma eval_reflectedVarianceSkewPolyOf_nonpos_of_explicit_factor_eq
  {p q : BiPoly}
  {X Y : Real}
-- given
  (hX : 1 ≤ X)
  (hY : 1 ≤ Y)
  (hfactor : (clearedSkewPolyOf p).eval X Y = q.eval X Y * (X ^ 2 - 1) * (Y ^ 2 - 1))
  (hq : 0 ≤ q.eval X Y) :
-- imply
  (reflectedVarianceSkewPolyOf p).eval X Y ≤ 0 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.eval_reflectedVarianceSkewPolyOf_nonpos_of_explicit_factor p q X Y hX hY hfactor hq


-- created on 2026-10-23
