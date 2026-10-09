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

import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Prime.Defs

/-!
# Conditions for simultaneous prime values of polynomials

This file adapts `BunyakovskyCondition` and `SchinzelCondition` from
[`FormalConjecturesForMathlib/Algebra/Polynomial/Basic.lean`](https://github.com/google-deepmind/formal-conjectures/blob/62f56e8e4dab933a720f649721875c478b0ecf1c/FormalConjecturesForMathlib/Algebra/Polynomial/Basic.lean)
at commit `62f56e8e4dab933a720f649721875c478b0ecf1c`.

The local adaptation places the reusable predicates in namespace `Polynomial`
and gives the module a purpose-specific name. The mathematical definitions are
unchanged.
-/


namespace Polynomial

/-- A nonconstant irreducible integer polynomial with positive leading coefficient. -/
def BunyakovskyCondition (f : ℤ[X]) : Prop :=
  1 ≤ f.degree ∧ Irreducible f ∧ 0 < f.leadingCoeff

/-- A finite family of integer polynomials has no fixed prime divisor. -/
def SchinzelCondition (fs : Finset ℤ[X]) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ f ∈ fs, ¬(p : ℤ) ∣ f.eval (n : ℤ)

end Polynomial
