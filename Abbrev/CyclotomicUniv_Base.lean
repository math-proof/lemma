import Mathlib

set_option autoImplicit false

noncomputable section

open Polynomial

namespace CyclotomicUniv

variable (N : ℕ)

abbrev R₀ : Type := AdjoinRoot (cyclotomic N ℤ)

section Basic

variable [NeZero N]

end Basic

section Lift

variable {N} [NeZero N] {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z N)
include hz

end Lift

end CyclotomicUniv

end
