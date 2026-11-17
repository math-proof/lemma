/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.v1.Atlas.EllipticCurves.code.FiniteFields.Part5
public import Lemma.Complex.Atlas.v1.EllipticCurves.code.FiniteFields
public import Mathlib.FieldTheory.Finite.Extension
public import Instance.v1.Atlas.EllipticCurves.code.FiniteFieldArith


public section

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
