import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Localization.Away.Basic

namespace Ihara

open Matrix

open scoped MatrixGroups

abbrev ZAway (q : ℕ) : Type := Localization.Away (q : ℤ)

variable (N q : ℕ)

end Ihara
