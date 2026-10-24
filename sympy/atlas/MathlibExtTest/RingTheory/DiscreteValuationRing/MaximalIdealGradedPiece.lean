/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DiscreteValuationRing/MaximalIdealGradedPiece.lean -/

/-
Author: Muse Code
-/

import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealGradedPiece
import Lemma.Int.DiscreteValuationRing.MaximalIdealGradedPiece

/-!
# Tests for maximal-ideal graded pieces of a discrete valuation ring

These examples exercise the three public API components of
`MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealGradedPiece`: the
`MaximalIdealGradedPiece` type abbreviation, the residue-field-linear
equivalence `residueFieldLinearEquivMaximalIdealGradedPiece`, and the
`finrank_maximalIdealGradedPiece` theorem, including a degree-zero
specialization.
-/


open IsLocalRing IsDiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The type abbreviation unfolds to the quotient of `𝔪 ^ i` by `𝔪 • ⊤`. -/
example (i : ℕ) :
    MaximalIdealGradedPiece R i =
      (((maximalIdeal R) ^ i : Ideal R) ⧸
        (maximalIdeal R • ⊤ :
          Submodule R ((maximalIdeal R) ^ i : Ideal R))) :=
  rfl

/-- The residue-field-linear equivalence applies as stated. -/
noncomputable example (i : ℕ) :
    ResidueField R ≃ₗ[ResidueField R] MaximalIdealGradedPiece R i :=
  residueFieldLinearEquivMaximalIdealGradedPiece R i

/-- The finrank theorem applies as stated. -/
example (i : ℕ) :
    Module.finrank (ResidueField R) (MaximalIdealGradedPiece R i) = 1 :=
  finrank_maximalIdealGradedPiece R i

/-- Degree-zero specialization: the equivalence out of the residue field. -/
noncomputable example : ResidueField R ≃ₗ[ResidueField R] MaximalIdealGradedPiece R 0 :=
  residueFieldLinearEquivMaximalIdealGradedPiece R 0

/-- Degree-zero specialization: the finrank statement. -/
example : Module.finrank (ResidueField R) (MaximalIdealGradedPiece R 0) = 1 :=
  finrank_maximalIdealGradedPiece R 0
