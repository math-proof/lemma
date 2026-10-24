/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/MaxPrimeFac.lean -/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Lattice.Nat

namespace Nat

/-- The greatest prime divisor of a natural number.

This is totalized by the convention `maxPrimeFac 0 = 0` and `maxPrimeFac 1 = 0`. The value at
zero is only a computational convention: every prime divides zero, so zero has no greatest prime
divisor. The value at one records that one has no prime divisors. -/
def maxPrimeFac (n : ℕ) : ℕ := n.primeFactors.sup id

example : maxPrimeFac 0 = 0 := by decide +kernel
example : maxPrimeFac 1 = 0 := by decide +kernel
example : maxPrimeFac 12 = 3 := by decide +kernel
example : maxPrimeFac 97 = 97 := by decide +kernel
example : maxPrimeFac 125 = 5 := by decide +kernel
example : maxPrimeFac 360 = 5 := by decide +kernel
end Nat
