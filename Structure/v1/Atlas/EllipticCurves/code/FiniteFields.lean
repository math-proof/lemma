/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Def.v1.Atlas.EllipticCurves.code.FiniteFields.Part4


section Definition_3_14

variable (p : ℕ) [Fact p.Prime]

open Polynomial

/-- A family `fam : ∀ n > 0, 𝔽_p[X]` is a Conway polynomial system if it
satisfies the recursive definition (Definition 3.16): the degree-one case is
`X - r` for the least primitive root `r`; each higher polynomial is primitive,
has the right degree, is compatible with smaller members, and is minimal under
the Conway lex order among such primitives. -/
structure IsConwayPolynomialSystem
    (fam : ∀ n : ℕ, 0 < n → (ZMod p)[X]) : Prop where
  degree_one : ∃ (r : ℕ), 0 < r ∧ r < p ∧
    orderOf ((r : ZMod p) : ZMod p) = p - 1 ∧
    (∀ s : ℕ, 0 < s → s < r → orderOf ((s : ZMod p) : ZMod p) ≠ p - 1) ∧
    fam 1 (by omega) = X - C (r : ZMod p)
  isPrimitive : ∀ n : ℕ, ∀ (hn : 0 < n), 1 < n →
    (fam n hn).IsPrimitivePolynomial p
  hasDegree : ∀ n : ℕ, ∀ (hn : 0 < n), 1 < n → (fam n hn).natDegree = n
  compatible : ∀ n : ℕ, ∀ (hn : 0 < n), 1 < n →
    ConwayCompatible p (fun m hm => fam m hm) n (fam n hn)
  isLeast : ∀ n : ℕ, ∀ (hn : 0 < n), 1 < n →
    ∀ g : (ZMod p)[X],
      g.IsPrimitivePolynomial p → g.natDegree = n →
      ConwayCompatible p (fun m hm => fam m hm) n g →
      ¬ conwayLT p g (fam n hn)

end Definition_3_14
