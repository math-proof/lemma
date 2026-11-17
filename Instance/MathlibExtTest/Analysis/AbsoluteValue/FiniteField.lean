/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/AbsoluteValue/FiniteField.lean -/

module

public import Theorem.Analysis.AbsoluteValue.FiniteField
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open AbsoluteValue

variable {K : Type*} [Field K]


instance : Fact (Nat.Prime 5) := ⟨by decide⟩

