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
import Structure.v1.Atlas.EllipticCurves.code.FiniteFieldArith.Part2


namespace FiniteFieldArith

variable (intMulCost : ℕ → ℕ)

namespace Polynomial

section SqfreeFactorization

variable {k : Type*} [Field k]

open Classical

/-- A single iteration of the distinct-degree factorization loop: extract the
product of degree-`j` irreducible factors of the current `remaining`, and append
it to the factor list. -/
noncomputable def distinctDegreeIter (st : DistinctDegreeState k) (j : ℕ) :
    DistinctDegreeState k :=
  let g := EuclideanDomain.gcd st.remaining (xPowCardPowSubX k j)
  { remaining := st.remaining / g
    factors := st.factors ++ [g] }

/-- Iterate distinct-degree factorization for `j = 1, 2, …, n`, starting from `f`. -/
noncomputable def distinctDegreeLoop (f : k[X]) : ℕ → DistinctDegreeState k
  | 0 => { remaining := f, factors := [] }
  | n + 1 => distinctDegreeIter (distinctDegreeLoop f n) (n + 1)

/-- Top-level distinct-degree factorization (step 2 of Algorithm 3.47): for input
`f`, run the loop up to degree `deg f` and return the list of degree-`j` factors. -/
noncomputable def distinctDegreeFactorize (f : k[X]) : List (k[X]) :=
  (distinctDegreeLoop f f.natDegree).factors

end SqfreeFactorization
end Polynomial
end FiniteFieldArith
