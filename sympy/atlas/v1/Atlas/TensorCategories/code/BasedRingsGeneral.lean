/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRingsGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.BasedRings
import Lemma.Category.Atlas.v1.TensorCategories.code.BasedRings

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Finset

universe v u

namespace CategoricalMultitensorData

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [cmd : CategoricalMultitensorData κ C]

/-- Packages the data of a `CategoricalMultitensorData` (fusion coefficients, unit set,
duality involution, and their compatibilities) into a `BasedRingDef`, i.e. the data of
a based ring on `cmd.ι`. -/
def toBasedRingDef : BasedRingDef cmd.ι where
  N := cmd.N
  I₀ := cmd.I₀
  finite_support := fun _ _ => Set.toFinite _
  sum_I₀_mul_left := cmd.N_sum_I₀_mul_left
  sum_I₀_mul_right := cmd.N_sum_I₀_mul_right
  assoc_finite := fun i j k l =>
    ⟨Set.toFinite _, Set.toFinite _,
     by rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]; exact cmd.N_assoc i j k l⟩
  star := cmd.star
  star_star := cmd.star_star
  duality_trace := cmd.N_duality_trace
  star_anti := cmd.N_star_anti

/-- Packages a `CategoricalMultitensorData` into a `MultifusionRingDef`, i.e. the data of
a multifusion ring on `cmd.ι`. -/
def toMultifusionRingDef : MultifusionRingDef cmd.ι where
  N := cmd.N
  I₀ := cmd.I₀
  star := cmd.star
  star_star := cmd.star_star
  assoc := cmd.N_assoc
  sum_I₀_mul_left := cmd.N_sum_I₀_mul_left
  sum_I₀_mul_right := cmd.N_sum_I₀_mul_right
  duality_trace := cmd.N_duality_trace
  star_anti := cmd.N_star_anti
