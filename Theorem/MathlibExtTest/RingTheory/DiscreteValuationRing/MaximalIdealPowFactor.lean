/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DiscreteValuationRing/MaximalIdealPowFactor.lean -/

/-
Author: Muse Code
-/

import Def.RingTheory.DiscreteValuationRing.MaximalIdealPowFactor.Part3
import Lemma.Int.DiscreteValuationRing.MaximalIdealPowFactor
open IsLocalRing

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]

/-!
# Tests for residue-field maximal-ideal-power quotients

These examples exercise the public API of
`MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealPowFactor`: the
`ResidueFieldMaximalIdealPowQuotient` type abbreviation, the residue-field
algebra instances, the factor map
`factorResidueFieldMaximalIdealPowQuotient`, its surjectivity theorem, and its
representative formula, plus the quotient-ring equivalence
`residueFieldMaximalIdealPowQuotientEquivPow` and its representative formula,
and the graded-piece kernel equivalence
`residueFieldLinearEquivMaximalIdealGradedPieceKerFactor` and its
representative formula
`residueFieldLinearEquivMaximalIdealGradedPieceKerFactor_mk`.
-/


/-- The residue-field algebra structure synthesizes on the quotient. -/
example (n : ℕ) :
    Algebra (ResidueField A) (ResidueFieldMaximalIdealPowQuotient A B n) :=
  inferInstance

/-- The factor map applies to a quotient representative. -/
noncomputable example (n : ℕ) (b : B) :
    ResidueFieldMaximalIdealPowQuotient A B n :=
  factorResidueFieldMaximalIdealPowQuotient A B n
    (Ideal.Quotient.mk _ b)

/-- The surjectivity theorem applies as stated. -/
example (n : ℕ) :
    Function.Surjective (factorResidueFieldMaximalIdealPowQuotient A B n) :=
  factorResidueFieldMaximalIdealPowQuotient_surjective A B n

/-- The collapse helper applies as stated. -/
example (n : ℕ)
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n) :
    (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ n :
      Ideal B) = maximalIdeal B ^ n :=
  maximalIdealPowQuotientIdeal_eq A B n h

/-- The representative formula applies as stated. -/
example (n : ℕ) (b : B) :
    factorResidueFieldMaximalIdealPowQuotient A B n
        (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ b :=
  factorResidueFieldMaximalIdealPowQuotient_mk A B n b

/-- The quotient-ring equivalence has the stated type. -/
noncomputable example (n : ℕ)
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n) :
    ResidueFieldMaximalIdealPowQuotient A B n ≃+* B ⧸ maximalIdeal B ^ n :=
  residueFieldMaximalIdealPowQuotientEquivPow A B n h

/-- The quotient-ring equivalence fixes representatives. -/
noncomputable example (n : ℕ)
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n)
    (b : B) :
    residueFieldMaximalIdealPowQuotientEquivPow A B n h
        (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ b :=
  residueFieldMaximalIdealPowQuotientEquivPow_mk A B n h b

/-- The graded-piece kernel equivalence has the stated type. -/
noncomputable example (n : ℕ)
    (hSucc : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
      maximalIdeal B ^ (n + 1))
    [IsLocalHom (algebraMap A B)]
    [Module (ResidueField A)
      (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)]
    [IsScalarTower (ResidueField A) (ResidueField B)
      (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)] :
    IsDiscreteValuationRing.MaximalIdealGradedPiece B n ≃ₗ[ResidueField A]
      LinearMap.ker (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap :=
  residueFieldLinearEquivMaximalIdealGradedPieceKerFactor A B n hSucc

/-- The kernel equivalence sends a graded representative to the corresponding
quotient representative. -/
example (n : ℕ)
    (hSucc : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
      maximalIdeal B ^ (n + 1))
    [IsLocalHom (algebraMap A B)]
    [Module (ResidueField A)
      (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)]
    [IsScalarTower (ResidueField A) (ResidueField B)
      (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)]
    (z : (maximalIdeal B ^ n : Ideal B)) :
    ((residueFieldLinearEquivMaximalIdealGradedPieceKerFactor A B n hSucc
        (Submodule.Quotient.mk z) :
        ResidueFieldMaximalIdealPowQuotient A B (n + 1)) =
      Ideal.Quotient.mk _ (z : B)) :=
  residueFieldLinearEquivMaximalIdealGradedPieceKerFactor_mk A B n hSucc z

