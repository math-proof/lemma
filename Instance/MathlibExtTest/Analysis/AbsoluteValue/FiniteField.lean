/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/AbsoluteValue/FiniteField.lean -/


import sympy.atlas.Analysis.AbsoluteValue.FiniteField
import Mathlib.FieldTheory.Finite.Basic
open AbsoluteValue

variable {K : Type*} [Field K]


instance : Fact (Nat.Prime 5) := ⟨by decide⟩

