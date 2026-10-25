/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/OperatorCommutativity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Lemma.List.Any_And_IsReduced_EraseIdx.of.LtLengthMulWordProdSimple_Length_WordProd.IsReduced
import Lemma.Int.LengthMulMulSimpleSimple.gt.LengthMulSimple.of.GtLengthMul_Simple_Length.LtLengthMulSimple_Length
import Def.v1.Atlas.Buildings.code.HeckeAlgebra.Generic.Part2
import Def.v1.Atlas.Buildings.code.HeckeAlgebra.OperatorCommutativity
open scoped Classical


namespace HeckeAlgebra

variable {B : Type*} [DecidableEq B] [Fintype B]
  {M : CoxeterMatrix B} {R : Type*} [CommRing R]


/-- Data of a candidate Hecke-algebra structure on a free $R$-module, packaging both
left and right length-up/length-down rules together with module operations,
two-sided generator associativity, and conjugacy invariance of $(a_s, b_s)$. -/
structure FreeModuleHeckeData (M : CoxeterMatrix B') (R : Type*) [CommRing R] where
  carrier : Type*
  basis : M.Group → carrier
  smul : R → carrier → carrier
  mul : carrier → carrier → carrier
  add : carrier → carrier → carrier
  a : B' → R
  b : B' → R
  left_length_up : ∀ (s : B') (w : M.Group),
    M.toCoxeterSystem.length (M.toCoxeterSystem.simple s * w) > M.toCoxeterSystem.length w →
    mul (basis (M.toCoxeterSystem.simple s)) (basis w) = basis (M.toCoxeterSystem.simple s * w)
  left_length_down : ∀ (s : B') (w : M.Group),
    M.toCoxeterSystem.length (M.toCoxeterSystem.simple s * w) < M.toCoxeterSystem.length w →
    mul (basis (M.toCoxeterSystem.simple s)) (basis w) =
      add (smul (a s) (basis w)) (smul (b s) (basis (M.toCoxeterSystem.simple s * w)))
  right_length_up : ∀ (t : B') (w : M.Group),
    M.toCoxeterSystem.length (w * M.toCoxeterSystem.simple t) > M.toCoxeterSystem.length w →
    mul (basis w) (basis (M.toCoxeterSystem.simple t)) = basis (w * M.toCoxeterSystem.simple t)
  right_length_down : ∀ (t : B') (w : M.Group),
    M.toCoxeterSystem.length (w * M.toCoxeterSystem.simple t) < M.toCoxeterSystem.length w →
    mul (basis w) (basis (M.toCoxeterSystem.simple t)) =
      add (smul (a t) (basis w)) (smul (b t) (basis (w * M.toCoxeterSystem.simple t)))
  identity_left : ∀ (x : carrier), mul (basis 1) x = x
  identity_right : ∀ (x : carrier), mul x (basis 1) = x
  mul_add_right : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  mul_add_left : ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)
  mul_smul_right : ∀ (r : R) x y, mul x (smul r y) = smul r (mul x y)
  smul_mul_left : ∀ (r : R) x y, mul (smul r x) y = smul r (mul x y)
  add_comm : ∀ x y, add x y = add y x
  add_assoc' : ∀ x y z, add (add x y) z = add x (add y z)
  smul_add : ∀ (r : R) x y, smul r (add x y) = add (smul r x) (smul r y)
  smul_smul : ∀ (r₁ r₂ : R) x, smul r₁ (smul r₂ x) = smul (r₁ * r₂) x
  basis_span : ∀ (P : carrier → Prop),
    (∀ w, P (basis w)) →
    (∀ x y, P x → P y → P (add x y)) →
    (∀ (r : R) x, P x → P (smul r x)) →
    ∀ z, P z
  conj_inv : ∀ (s₁ s₂ : B') (w : M.Group),
    w * M.toCoxeterSystem.simple s₁ * w⁻¹ = M.toCoxeterSystem.simple s₂ →
    a s₁ = a s₂ ∧ b s₁ = b s₂
  gen_left_assoc : ∀ (s : B') (x y : carrier),
    mul (basis (M.toCoxeterSystem.simple s)) (mul x y) =
      mul (mul (basis (M.toCoxeterSystem.simple s)) x) y
  gen_right_assoc : ∀ (t : B') (x y : carrier),
    mul (mul x y) (basis (M.toCoxeterSystem.simple t)) =
      mul x (mul y (basis (M.toCoxeterSystem.simple t)))

end HeckeAlgebra
