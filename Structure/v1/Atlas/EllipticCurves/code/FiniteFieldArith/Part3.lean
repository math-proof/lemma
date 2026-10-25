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
import Def.v1.Atlas.EllipticCurves.code.FiniteFieldArith.Part3


namespace FiniteFieldArith

variable (intMulCost : ℕ → ℕ)

namespace Polynomial

section SqfreeFactorization

variable {k : Type*} [Field k]

open Classical

/-- Distinct-degree factorization specification (step 2 of Algorithm 3.47):
`f` factors as `∏ h_j` where each `h_j` is a (possibly trivial) squarefree
product of irreducibles all of degree `j+1`, and the `h_j` are pairwise coprime. -/
structure IsDistinctDegreeFactorization (f : k[X]) (d : ℕ) (hs : Fin d → k[X]) : Prop where
  prod_eq : f = ∏ i : Fin d, hs i
  irred_deg : ∀ (j : Fin d) (g : k[X]), Irreducible g → g ∣ hs j → g.natDegree = j.val + 1
  squarefree : ∀ j : Fin d, hs j = 1 ∨ Squarefree (hs j)
  coprime : ∀ i j : Fin d, i ≠ j → IsCoprime (hs i) (hs j)

end SqfreeFactorization
end Polynomial
end FiniteFieldArith
