import Mathlib
import Def.ModularCurve_JqCoeff
import Def.ModularCurve_LaurentCoeff
import Class.AlgebraicCurve_DivisorClassGroup
import Lemma.ModularCurve.CoeffSemilinearAut
import Lemma.ModularCurve.QAdicPlaceMod

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve

namespace ModularCurve


section QExpandAlg

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def qExpandAlgHomC : LaurentSeries K →ₐ[K] LaurentSeries K where
  __ := qExpand K N
  commutes' c := by
    show qExpand K N (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

end QExpandAlg

section FunctionField

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def divisorExpansionsC : Set (LaurentSeries K) :=
  {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = qExpand K d (jqModC K)}

omit [NeZero N] in

def modularFunctionFieldFullC : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K (divisorExpansionsC K N)

end FunctionField

end ModularCurve

end
