import Mathlib

open Quaternion

namespace QuaternionAlgebra

section ReducedNorm

variable {R : Type*} [CommRing R] {a b : R}

def nrd (x : ℍ[R, a, b]) : R :=
  x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2

def trd (x : ℍ[R, a, b]) : R := 2 * x.re

end ReducedNorm

end QuaternionAlgebra
