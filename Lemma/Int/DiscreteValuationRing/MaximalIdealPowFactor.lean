import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealPowFactor
open IsLocalRing


/--
[factorResidueFieldMaximalIdealPowQuotient_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowFactor.lean)
-/
@[path]
lemma factorResidueFieldMaximalIdealPowQuotient_surjective
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
  {n : ℕ} :
-- imply
  Function.Surjective (factorResidueFieldMaximalIdealPowQuotient A B n) :=
-- proof
  Ideal.Quotient.factor_surjective (maximalIdealPowQuotientIdeal_le A B n)

/--
[residueFieldLinearEquivMaximalIdealGradedPieceKerFactor_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowFactor.lean)
-/
@[path]
lemma residueFieldLinearEquivMaximalIdealGradedPieceKerFactor_mk
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
  {n : ℕ} [Module (ResidueField A) (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)] [IsScalarTower (ResidueField A) (ResidueField B) (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)]
  {z : (maximalIdeal B ^ n : Ideal B)}
-- given
  (hSucc : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ (n + 1)) :
-- imply
  ((residueFieldLinearEquivMaximalIdealGradedPieceKerFactor A B n hSucc
    (Submodule.Quotient.mk z) :
    ResidueFieldMaximalIdealPowQuotient A B (n + 1)) =
    Ideal.Quotient.mk _ (z : B)) :=
-- proof
  rfl

/--
[maximalIdealPowQuotientIdeal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowFactor.lean)
-/
@[path]
private lemma maximalIdealPowQuotientIdeal_eq_eq
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
  {n : ℕ}
-- given
  (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n) :
-- imply
  (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ n :
    Ideal B) = maximalIdeal B ^ n := by
-- proof
  apply maximalIdealPowQuotientIdeal_eq A B n h

/--
[maximalIdealPowQuotientIdeal_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowFactor.lean)
-/
@[path]
private lemma maximalIdealPowQuotientIdeal_le_eq
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
  {n : ℕ} :
-- imply
  (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ (n + 1) :
    Ideal B) ≤
    Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ n := by
-- proof
  apply maximalIdealPowQuotientIdeal_le A B n

/--
[factorResidueFieldMaximalIdealPowQuotient_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowFactor.lean)
-/
@[path]
private lemma factorResidueFieldMaximalIdealPowQuotient_mk_eq
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
  {n : ℕ}
  {b : B} :
-- imply
  factorResidueFieldMaximalIdealPowQuotient A B n
    (Ideal.Quotient.mk _ b) =
    Ideal.Quotient.mk _ b := by
-- proof
  apply factorResidueFieldMaximalIdealPowQuotient_mk A B n b

/--
[residueFieldMaximalIdealPowQuotientEquivPow_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowFactor.lean)
-/
@[path]
private lemma residueFieldMaximalIdealPowQuotientEquivPow_mk_eq
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
  {n : ℕ}
  {b : B}
-- given
  (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n) :
-- imply
  residueFieldMaximalIdealPowQuotientEquivPow A B n h
    (Ideal.Quotient.mk _ b) =
    Ideal.Quotient.mk _ b := by
-- proof
  apply residueFieldMaximalIdealPowQuotientEquivPow_mk A B n h b


-- created on 2026-10-20
-- updated on 2026-10-23
