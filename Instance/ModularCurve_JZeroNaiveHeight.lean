-- Carved from Lemma/Definitions/Def_ModularCurve_JZeroNaiveHeight.lean: instance decls only.

module

public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.Height.NumberField
public import Instance.Compat_Mathlib430

@[expose] public section

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
