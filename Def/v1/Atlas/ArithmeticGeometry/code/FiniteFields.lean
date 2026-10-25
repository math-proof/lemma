/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


/-- The number of affine solutions $(x, y, z) \in K^3$ to the diagonal ternary
quadratic form $aX^2 + bY^2 + cZ^2 = 0$. -/
noncomputable def affineSolCount (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (a b c : K) : ℕ :=
  Fintype.card { v : Fin 3 → K // a * (v 0) ^ 2 + b * (v 1) ^ 2 + c * (v 2) ^ 2 = 0 }

/-- The number of projective points on the conic $aX^2 + bY^2 + cZ^2 = 0$,
obtained from the affine count by removing the origin and quotienting by the
action of $K^\times$. -/
noncomputable def projConicCount (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (a b c : K) : ℕ :=
  (affineSolCount K a b c - 1) / (Fintype.card K - 1)

/-- Fibered description of solutions of $aX_0^2 + bX_1^2 + cX_2^2 = 0$ over the
projection onto the last two coordinates: equivalent to a $\Sigma$-type indexed
by $(y, z)$ of solutions to $aX^2 + (b y^2 + c z^2) = 0$. -/
noncomputable def fiberEquivOdd (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (a b c : K) :
    { v : Fin 3 → K // a * (v 0) ^ 2 + b * (v 1) ^ 2 + c * (v 2) ^ 2 = 0 } ≃
    Σ (p : K × K), { x : K // a * x ^ 2 + (b * p.1 ^ 2 + c * p.2 ^ 2) = 0 } where
  toFun := fun ⟨v, hv⟩ => ⟨(v 1, v 2), v 0, by linear_combination hv⟩
  invFun := fun ⟨⟨y, z⟩, x, hx⟩ => ⟨![x, y, z], by
    have h0 : (![x, y, z] : Fin 3 → K) 0 = x := by simp
    have h1 : (![x, y, z] : Fin 3 → K) 1 = y := by simp
    have h2 : (![x, y, z] : Fin 3 → K) 2 = z := by simp
    rw [h0, h1, h2]; linear_combination hx⟩
  left_inv := fun ⟨v, hv⟩ => by
    apply Subtype.ext; funext i; fin_cases i <;> simp
  right_inv := fun ⟨⟨y, z⟩, x, hx⟩ => by
    simp only [Sigma.mk.inj_iff, Prod.mk.injEq]
    refine ⟨⟨by simp, by simp⟩, ?_⟩; simp

/-- A diagonal conic $aX^2 + bY^2 + cZ^2 = 0$ is *geometrically irreducible*
when $c \neq 0$. -/
def DiagConicIsGeomIrreducible {K : Type*} [Field K] (_a _b c : K) : Prop :=
  c ≠ 0

/-- A diagonal conic $aX^2 + bY^2 + cZ^2 = 0$ *splits over the base field* $K$
when $c = 0$ and $-b/a$ is a square in $K$. -/
def DiagConicIsSplitOverBase {K : Type*} [Field K] (a b c : K) : Prop :=
  c = 0 ∧ IsSquare (-b * a⁻¹)

/-- A diagonal conic $aX^2 + bY^2 + cZ^2 = 0$ *splits only over a quadratic
extension* when $c = 0$ and $-b/a$ is *not* a square in $K$. -/
def DiagConicIsSplitOverExtension {K : Type*} [Field K] (a b c : K) : Prop :=
  c = 0 ∧ ¬IsSquare (-b * a⁻¹)

