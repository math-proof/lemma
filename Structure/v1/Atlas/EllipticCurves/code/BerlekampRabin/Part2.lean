/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Def.v1.Atlas.EllipticCurves.code.BerlekampRabin.Part3
open Polynomial Finset


namespace BerlekampRabin

section YunCorrectness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Correctness predicate for the output of `cantorZassenhausAlgorithm`: the indexed
family `factors : Fin n → F[X]` consists of irreducibles, `f = ∏ (factors i)^(mult i)`,
multiplicities are positive, and distinct indices give non-associated factors. -/
structure IsIrreducibleFactorization (f : F[X]) (n : ℕ)
    (factors : Fin n → F[X]) (multiplicities : Fin n → ℕ) : Prop where
  irred : ∀ i : Fin n, Irreducible (factors i)
  prod_eq : f = ∏ i : Fin n, (factors i) ^ (multiplicities i)
  mult_pos : ∀ i : Fin n, 0 < multiplicities i
  pairwise : ∀ i j : Fin n, i ≠ j → ¬ Associated (factors i) (factors j)

end YunCorrectness
end BerlekampRabin
