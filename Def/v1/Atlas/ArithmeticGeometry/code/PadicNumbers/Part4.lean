/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.DirectedInverseSystem
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib
import Theorem.v1.Atlas.ArithmeticGeometry.code.PadicNumbers


namespace DiscreteValuation

variable {R : Type*} [CommRing R] (v : DiscreteValuation R)

/-- The subring of $\prod_n \mathbb{Z}/p^n\mathbb{Z}$ consisting of compatible sequences with
respect to all reduction maps $\mathbb{Z}/p^n\mathbb{Z} \to \mathbb{Z}/p^m\mathbb{Z}$ for
$m \le n$. This is the explicit inverse-limit model for $\mathbb{Z}_p$. -/
def zmodInvLimSubring : Subring (∀ n, ZMod (p ^ n)) where
  carrier := { a | ∀ (m n : ℕ) (h : m ≤ n),
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))) (a n) = a m }
  mul_mem' := fun {a b} ha hb m n hmn => by
    simp only [Pi.mul_apply, map_mul, ha m n hmn, hb m n hmn]
  one_mem' := fun m n hmn => by
    simp only [Pi.one_apply, map_one]
  add_mem' := fun {a b} ha hb m n hmn => by
    simp only [Pi.add_apply, map_add, ha m n hmn, hb m n hmn]
  zero_mem' := fun m n hmn => by
    simp only [Pi.zero_apply, map_zero]
  neg_mem' := fun {a} ha m n hmn => by
    simp only [Pi.neg_apply, map_neg, ha m n hmn]

/-- The $n$-th projection ring homomorphism from `zmodInvLimSubring` to $\mathbb{Z}/p^n\mathbb{Z}$.
-/
def invLimProj (n : ℕ) : (zmodInvLimSubring p) →+* ZMod (p ^ n) :=
  (Pi.evalRingHom (fun n => ZMod (p ^ n)) n).comp (zmodInvLimSubring p).subtype

end DiscreteValuation
