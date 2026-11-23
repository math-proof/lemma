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
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.FiniteFields
public import Mathlib.FieldTheory.Finite.Extension
public import Def.v1.Atlas.EllipticCurves.code.FiniteFieldArith.Part2


public section

namespace FiniteFieldArith

variable (intMulCost : ℕ → ℕ)

namespace Polynomial

section SqfreeFactorization

variable {k : Type*} [Field k]

open Classical

/-- State for the distinct-degree factorization loop: the polynomial still left
to factor and the list of degree-`j` partial products accumulated so far. -/
structure DistinctDegreeState (k : Type*) [Field k] where
  remaining : k[X]
  factors : List (k[X])

end SqfreeFactorization
end Polynomial
end FiniteFieldArith
