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
public import Def.v1.Atlas.EllipticCurves.code.FiniteFieldArith.Part3


public section

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
