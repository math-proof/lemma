-- Carved from Lemma/Definitions/Def_ModularCurve_JZeroNaiveHeight.lean: instance decls only.
import Lemma.ModularCurve.AtkinLehner
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Height.NumberField
import Instance.Compat_Mathlib430

noncomputable section

open AlgebraicCurve Polynomial

namespace ModularCurve

variable (N : ℕ) [NeZero N]

instance numberField_of_finiteDimensional (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] : NumberField K :=
  NumberField.mk

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]

variable {N K}

end ModularCurve

end
