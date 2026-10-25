/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecCategoricalFusionData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.TensorCategories.code.VecSemisimple.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.VecSemisimple
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Theorem.v1.Atlas.TensorCategories.code.VecCategoricalFusionData
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Module TensorProduct

universe u


noncomputable section

namespace VecCategoricalFusionData

variable (k : Type u) [Field k]

/-- `FGModuleCat k` is a categorical fusion category with the single simple object `k`,
trivial fusion rules (`k ⊗ k = k`), and self-dual involution. This packages
`Vec_k` as the rank-one fusion category. -/
instance : CategoricalFusionData k (FGModuleCat.{u} k) where
  ι := Fin 1
  S := fun _ => FGModuleCat.of k k
  S_simple := fun _ => VecSemisimple.simple_of_k k
  S_complete := fun X hX => ⟨0, ⟨@VecSemisimple.simple_iso_of_k k _ X hX⟩⟩
  S_distinct := fun i j _ => Subsingleton.elim i j
  unitIdx := 0
  unitIso := ⟨Iso.refl _⟩
  N := fun _ _ _ => 1
  star := id
  star_star := fun _ => rfl
  N_unit_mul := fun j m => by
    have hj := Subsingleton.elim j (0 : Fin 1)
    have hm := Subsingleton.elim m (0 : Fin 1)
    subst hj; subst hm; simp
  N_mul_unit := fun i m => by
    have hi := Subsingleton.elim i (0 : Fin 1)
    have hm := Subsingleton.elim m (0 : Fin 1)
    subst hi; subst hm; simp
  N_duality := fun i j => by
    have hi := Subsingleton.elim i (0 : Fin 1)
    have hj := Subsingleton.elim j (0 : Fin 1)
    subst hi; subst hj; simp
  N_assoc := fun _ _ _ _ => by simp
  N_star_transpose := fun _ _ _ => rfl
  N_eq_finrank := fun i j m => by
    have hi := Subsingleton.elim i (0 : Fin 1)
    have hj := Subsingleton.elim j (0 : Fin 1)
    have hm := Subsingleton.elim m (0 : Fin 1)
    subst hi; subst hj; subst hm
    exact (vec_hom_finrank k).symm


  mult := fun _ _ => 1
  mult_simple := fun i j => by
    have hi := Subsingleton.elim i (0 : Fin 1)
    have hj := Subsingleton.elim j (0 : Fin 1)
    subst hi; subst hj; simp
  mult_unit := fun j => by
    have hj := Subsingleton.elim j (0 : Fin 1)
    subst hj; simp
  mult_tensor := fun _ _ l => by
    have hl := Subsingleton.elim l (0 : Fin 1)
    subst hl; simp
  mult_iso := fun _ _ _ _ => rfl
  mult_nontrivial := fun _ => ⟨0, Nat.one_pos⟩

end VecCategoricalFusionData
end
