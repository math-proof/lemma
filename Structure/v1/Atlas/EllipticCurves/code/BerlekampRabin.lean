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
import Def.v1.Atlas.EllipticCurves.code.BerlekampRabin.Part2
open Polynomial Finset


namespace BerlekampRabin

section Bijection

variable {F : Type*} [Field F]

/-- The correctness predicate for a squarefree factorization (output of
Algorithm 3.46): the list is nonempty, recovers `f` as `∏ g_i^i`, each `g_i` is
squarefree, the factors are pairwise coprime, and the last factor is not `1`. -/
structure IsSquarefreeFactorization (f : F[X]) (factors : List (F[X])) : Prop where
  nonempty : factors ≠ []
  prod_eq : f = sqfreeProduct F factors
  sqfree : ∀ g ∈ factors, Squarefree g
  coprime : factors.Pairwise (fun g h => IsCoprime g h)
  last_ne_one : factors.getLast nonempty ≠ 1

end Bijection
end BerlekampRabin
