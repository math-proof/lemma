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
import Def.v1.Atlas.EllipticCurves.code.FiniteFieldArith.Part2


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
