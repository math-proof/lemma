import Mathlib

set_option autoImplicit false

open Matrix UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularForm

variable (M q : ℕ)

structure AtkinLehnerDatum : Type where

  R : ℕ

  hM : M = q * R

  a : ℤ

  b : ℤ

  bezout : (q : ℤ) * a - (R : ℤ) * b = 1

namespace AtkinLehnerDatum

variable {M q : ℕ} (W : AtkinLehnerDatum M q)


end AtkinLehnerDatum


end ModularForm

end
