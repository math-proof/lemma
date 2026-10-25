/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/BilinFormClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section30.Part4
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section30


noncomputable section

set_option autoImplicit false

namespace BilinFormZMod2

set_option synthInstance.maxHeartbeats 400000

/-- **The standard form of Proposition 30.6 (bilinear-form presentation).**
The bilinear form on `(F₂)^a × (F₂²)^b` given by the orthogonal direct sum
of `a` copies of the rank-one form `⟨x, y⟩ ↦ ∑ xᵢ yᵢ` (diagonal block) and
`b` copies of the hyperbolic plane `⟨x, y⟩ ↦ x₀y₁ + x₁y₀`.  Every
nondegenerate symmetric `F₂`-form is isometric to one of these
(see `exists_isometry_standardF2Form`). -/
def standardF2Form (a b : ℕ) :
    LinearMap.BilinForm (ZMod 2) ((Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2)) :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y => (∑ i, x.1 i * y.1 i) + ∑ j, (x.2 j 0 * y.2 j 1 + x.2 j 1 * y.2 j 0))
    (by
      intro x₁ x₂ y
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      ring)
    (by
      intro r x y
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring)
    (by
      intro x y₁ y₂
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      ring)
    (by
      intro r x y
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring)

end BilinFormZMod2

end


universe u in

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
open Finset in
/-- **The hyperbolic plane over `F₂`.**  The bilinear form on `(F₂)²` given
by `⟨x, y⟩ = x₀y₁ + x₁y₀`; its Gram matrix is `⎡⎣0 1 / 1 0⎤⎦`.  This is
the basic building block, alongside `⟨1⟩`, of the standard form in
Proposition 30.6, and it arises geometrically as the intersection form on
the middle cohomology of `S² × S²` with `F₂` coefficients. -/
def hyperbolicForm : LinearMap.BilinForm (ZMod 2) (Fin 2 → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => x 0 * y 1 + x 1 * y 0)
    (by intro x₁ x₂ y; simp [Pi.add_apply, add_mul]; ring)
    (by intro r x y; simp [Pi.smul_apply, smul_eq_mul]; ring)
    (by intro x y₁ y₂; simp [Pi.add_apply, mul_add]; ring)
    (by intro r x y; simp [Pi.smul_apply, smul_eq_mul]; ring)

/-- Linear-equivalence rearrangement used in the inductive proof of
Proposition 30.6: identifies a hyperbolic-block factor `(F₂²)` with a new
first coordinate of `(F₂²)^{b+1}`, leaving the diagonal block unchanged.
This is the `b`-axis analogue of `Fin.consLinearEquiv` for the diagonal
block, used in `case2_split` to convert the inductive output into the
desired standard form. -/
def finSuccEquiv (a b : ℕ) :
    ((Fin 2 → ZMod 2) × ((Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2))) ≃ₗ[ZMod 2]
      ((Fin a → ZMod 2) × (Fin (b + 1) → Fin 2 → ZMod 2)) :=
  { toFun := fun ⟨f, g, h⟩ => (g, Fin.cons f h)
    map_add' := by
      intro ⟨f₁, g₁, h₁⟩ ⟨f₂, g₂, h₂⟩
      ext : 1
      · rfl
      · ext j i
        refine Fin.cases ?_ (fun j' => ?_) j <;>
          simp [Fin.cons_zero, Fin.cons_succ, Pi.add_apply]
    map_smul' := by
      intro r ⟨f, g, h⟩
      ext : 1
      · simp
      · ext j i
        refine Fin.cases ?_ (fun j' => ?_) j <;>
          simp [Fin.cons_zero, Fin.cons_succ]
    invFun := fun ⟨g, k⟩ => (fun i => k 0 i, g, fun j => k j.succ)
    left_inv := by
      intro ⟨f, g, h⟩
      simp only [Fin.cons_zero, Fin.cons_succ]
    right_inv := by
      intro ⟨g, k⟩
      ext : 1
      · rfl
      · ext j i
        refine Fin.cases ?_ (fun j' => ?_) j <;>
          simp [Fin.cons_zero, Fin.cons_succ] }

