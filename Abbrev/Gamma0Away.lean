module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

namespace Ihara

open Matrix

open scoped MatrixGroups

abbrev ZAway (q : ℕ) : Type := Localization.Away (q : ℤ)

variable (N q : ℕ)

end Ihara
