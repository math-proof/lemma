/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Nullstellensatz
import Theorem.v1.Atlas.ArithmeticGeometry.code.AffineVarieties
variable (k : Type*) [Field k]


/-- A subset $V \subseteq \overline{k}^n$ is an algebraic subset if it equals $V(S)$ for
some set $S$ of polynomials. -/
def IsAlgebraicSubset (n : ℕ) (V : Set (AffineSpace_k k n)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin n) (AlgebraicClosure k)), V = AlgebraicSet k n S

/-- An algebraic set $V$ is irreducible if it is nonempty and whenever $V = V_1 \cup V_2$
with each $V_i$ algebraic, one of the $V_i$ equals $V$. -/
def IsIrreducibleAlgebraicSet (n : ℕ) (V : Set (AffineSpace_k k n)) : Prop :=
  V.Nonempty ∧
    ∀ V₁ V₂ : Set (AffineSpace_k k n),
      IsAlgebraicSubset k n V₁ → IsAlgebraicSubset k n V₂ →
      V = V₁ ∪ V₂ → V₁ = V ∨ V₂ = V

/-- The vanishing ideal $I(Z)$ of a subset $Z \subseteq k^\sigma$: polynomials in $k[x_\sigma]$
that vanish on every point of $Z$. -/
def idealOfAlgebraicSet (Z : Set (σ → k)) : Ideal (MvPolynomial σ k) where
  carrier := {f : MvPolynomial σ k | ∀ P ∈ Z, MvPolynomial.eval P f = 0}
  zero_mem' := fun _ _ => map_zero _
  add_mem' := fun {p q} hp hq x hx => by
    rw [map_add, hp x hx, hq x hx, add_zero]
  smul_mem' := fun r p hp x hx => by
    rw [smul_eq_mul, map_mul, hp x hx, mul_zero]

