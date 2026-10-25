/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.FieldTheory.Perfect
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.v1.Atlas.EllipticCurves.code.FiniteFields.Part5
import Lemma.Complex.Atlas.v1.EllipticCurves.code.FiniteFields
import Mathlib.FieldTheory.Finite.Extension
import Instance.v1.Atlas.EllipticCurves.code.FiniteFieldArith


namespace FiniteFieldArith

variable (intMulCost : ℕ → ℕ)

namespace Polynomial

section SqfreeFactorization

variable {k : Type*} [Field k]

open Classical

/-- Squarefree factorization data (Algorithm 3.46): a polynomial `f` is given a
squarefree factorization as `f = ∏_{i < m} g_i^{i+1}` where the `g_i` are
pairwise coprime squarefree polynomials, `m > 0`, and the top exponent factor
`g_{m-1}` is not the constant `1`. -/
structure IsSquarefreeFactorization (f : k[X]) (m : ℕ) (gs : Fin m → k[X]) : Prop where
  pos : 0 < m
  prod_eq : f = ∏ i : Fin m, (gs i) ^ (i.val + 1)
  squarefree : ∀ i : Fin m, Squarefree (gs i)
  coprime : ∀ i j : Fin m, i ≠ j → IsCoprime (gs i) (gs j)
  last_ne_one : gs ⟨m - 1, Nat.sub_one_lt_of_lt pos⟩ ≠ 1

/-- Loop state for Yun's algorithm (Algorithm 3.46): the running pair `(v_i, w_i)`
of polynomials whose GCD with the derivative-difference yields the next factor `g_i`. -/
structure YunState (k : Type*) [Field k] where
  v : k[X]
  w : k[X]

end SqfreeFactorization
end Polynomial
end FiniteFieldArith
