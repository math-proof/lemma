/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Derivation.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.CotangentLocal
open IsLocalRing


namespace CotangentDual

variable {R : Type*} [CommRing R] [IsLocalRing R]

variable {k : Type*} [Field k] [Algebra k R] [Algebra R k]

variable [IsScalarTower k R k]

lemma projMaxIdeal_add (hφ : Function.Surjective (algebraMap R k)) (x y : R) :
    projMaxIdeal hφ (x + y) = projMaxIdeal hφ x + projMaxIdeal hφ y := by
  apply Subtype.ext; simp [projMaxIdeal, map_add]; ring

lemma projMaxIdeal_smul (hφ : Function.Surjective (algebraMap R k)) (c : k) (x : R) :
    projMaxIdeal hφ (c • x) = c • projMaxIdeal hφ x := by
  apply Subtype.ext
  show (projMaxIdeal hφ (c • x)).val = c • (projMaxIdeal hφ x : R)
  simp only [projMaxIdeal, Subtype.coe_mk, Algebra.smul_def (R := k) (A := R),
    map_mul (f := algebraMap R k), algebraMap_comp_section, map_mul (f := algebraMap k R)]
  ring

lemma projMaxIdeal_one (hφ : Function.Surjective (algebraMap R k)) :
    projMaxIdeal hφ 1 = 0 := by
  apply Subtype.ext; simp [projMaxIdeal]

lemma projMaxIdeal_of_mem
    (hφ : Function.Surjective (algebraMap R k)) (m : maximalIdeal R) :
    (maximalIdeal R).toCotangent (projMaxIdeal hφ m.val) =
    (maximalIdeal R).toCotangent m := by
  rw [Ideal.toCotangent_eq]
  have hm : algebraMap R k m.val = 0 := mem_maximalIdeal_map_zero hφ m
  have hsub : (projMaxIdeal hφ m.val - m : maximalIdeal R).val = 0 := by
    simp only [projMaxIdeal, Submodule.coe_sub]; ring_nf; simp [hm]
  rw [show (projMaxIdeal hφ m.val - m : R) =
    (projMaxIdeal hφ m.val - m : maximalIdeal R).val from rfl, hsub]
  exact zero_mem _

lemma projCotangent_leibniz (hφ : Function.Surjective (algebraMap R k)) (x y : R) :
    (maximalIdeal R).toCotangent (projMaxIdeal hφ (x * y)) =
    algebraMap k R (algebraMap R k x) • (maximalIdeal R).toCotangent (projMaxIdeal hφ y) +
    algebraMap k R (algebraMap R k y) • (maximalIdeal R).toCotangent (projMaxIdeal hφ x) := by
  set d := projMaxIdeal hφ (x * y) -
      algebraMap k R (algebraMap R k x) • projMaxIdeal hφ y -
      algebraMap k R (algebraMap R k y) • projMaxIdeal hφ x
  have hd : (maximalIdeal R).toCotangent d = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    have hval : (d : R) = (projMaxIdeal hφ x).val * (projMaxIdeal hφ y).val := by
      change (projMaxIdeal hφ (x * y)).val -
        algebraMap k R (algebraMap R k x) * (projMaxIdeal hφ y).val -
        algebraMap k R (algebraMap R k y) * (projMaxIdeal hφ x).val =
        (projMaxIdeal hφ x).val * (projMaxIdeal hφ y).val
      simp only [projMaxIdeal, Subtype.coe_mk]
      have : algebraMap k R (algebraMap R k (x * y)) =
          algebraMap k R (algebraMap R k x) * algebraMap k R (algebraMap R k y) := by
        rw [map_mul, map_mul]
      rw [this]; ring
    rw [hval, pow_two]
    exact Ideal.mul_mem_mul (projMaxIdeal hφ x).2 (projMaxIdeal hφ y).2
  have expand : (maximalIdeal R).toCotangent d =
      (maximalIdeal R).toCotangent (projMaxIdeal hφ (x * y)) -
      algebraMap k R (algebraMap R k x) • (maximalIdeal R).toCotangent (projMaxIdeal hφ y) -
      algebraMap k R (algebraMap R k y) • (maximalIdeal R).toCotangent (projMaxIdeal hφ x) := by
    rw [map_sub, map_sub, map_smul, map_smul]
  rw [expand] at hd; rw [← sub_eq_zero, sub_add_eq_sub_sub]; exact hd

end CotangentDual
