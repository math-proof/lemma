/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DixmierLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Instance.v1.Atlas.LieGroups.code.DixmierLemma


noncomputable section

open Polynomial Finset Classical Finsupp Cardinal

universe u


def evalAt {k : Type u} [CommSemiring k] (A : Type u) [Semiring A] [Algebra k A]
    {M : Type u} [AddCommMonoid M] [Module A M] [Module k M] [IsScalarTower k A M]
    (v : M) : Module.End A M →ₗ[k] M where
  toFun T := T v
  map_add' _ _ := by simp
  map_smul' c T := by
    simp only [RingHom.id_apply]
    show (algebraMap k (Module.End A M) c * T) v = c • T v
    simp [Algebra.algebraMap_eq_smul_one]

def smulMap {k : Type u} [CommSemiring k] (A : Type u) [Semiring A] [Algebra k A]
    {M : Type u} [AddCommMonoid M] [Module A M] [Module k M] [IsScalarTower k A M]
    (v : M) : A →ₗ[k] M where
  toFun a := a • v
  map_add' a b := add_smul a b v
  map_smul' c a := smul_assoc c a v


def centerToEnd {k : Type u} [Field k] (A : Type u) [Ring A] [Algebra k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    Subalgebra.center k A →ₐ[k] Module.End A M where
  toFun z :=
    { toFun := fun m => (z : A) • m
      map_add' := fun m₁ m₂ => smul_add (z : A) m₁ m₂
      map_smul' := fun c m => by
        have hz := z.2
        simp only [Subalgebra.mem_center_iff] at hz
        show (↑z : A) • (c • m) = c • ((↑z : A) • m)
        rw [← mul_smul, ← mul_smul, hz c] }
  map_one' := by ext m; show (1 : A) • m = m; exact one_smul A m
  map_mul' z₁ z₂ := by
    ext m; show ((z₁ : A) * (z₂ : A)) • m = (z₁ : A) • ((z₂ : A) • m)
    exact mul_smul (z₁ : A) (z₂ : A) m
  map_zero' := by ext m; show (0 : A) • m = 0; exact zero_smul A m
  map_add' z₁ z₂ := by
    ext m; show ((z₁ : A) + (z₂ : A)) • m = (z₁ : A) • m + (z₂ : A) • m
    exact add_smul (z₁ : A) (z₂ : A) m
  commutes' c := by
    ext m
    change (algebraMap k A c) • m = (algebraMap k (Module.End A M) c) m
    conv_rhs => rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply]
    exact algebraMap_smul A c m

def centerCharacter {k : Type u} [Field k] (A : Type u) [Ring A] [Algebra k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    (hbij : Function.Bijective (algebraMap k (Module.End A M))) :
    Subalgebra.center k A →ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (Module.End A M)) hbij).symm.toAlgHom.comp
    (centerToEnd A)

end
