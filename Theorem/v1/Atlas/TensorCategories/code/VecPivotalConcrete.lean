/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecPivotalConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
import Lemma.Category.Atlas.v1.TensorCategories.code.VecInstances
import Lemma.Category.Atlas.v1.TensorCategories.code.VecDualMapBridge
import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2
import Theorem.v1.Atlas.TensorCategories.code.VecDualMapBridge
import Def.v1.Atlas.TensorCategories.code.VecPivotalConcrete
open CategoryTheory MonoidalCategory Module Category TensorCategories

universe u


noncomputable section

variable (k : Type u) [Field k]

section FixDiamond

attribute [-instance] BraidedCategory.rightRigidCategoryOfLeftRigidCategory

attribute [-instance] BraidedCategory.rigidCategoryOfLeftRigidCategory

attribute [-instance] RigidCategory.toRightRigidCategory

set_option maxHeartbeats 800000 in
/-- Naturality of the concrete double-dual isomorphism: for any `f : V ⟶ W` in
`FGModuleCat k`, the square involving `f` and the iterated right adjoint mate of `f`
commutes. -/
lemma vecDoubleDualIsoConcrete_naturality {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    f ≫ (vecDoubleDualIsoConcrete k W).hom =
      (vecDoubleDualIsoConcrete k V).hom ≫ (rightAdjointMate (rightAdjointMate f)) := by
  apply InducedCategory.Hom.ext
  apply ModuleCat.Hom.ext
  show (vecDoubleDualIsoConcrete k W).hom.hom.hom ∘ₗ f.hom.hom =
       (rightAdjointMate (rightAdjointMate f)).hom.hom ∘ₗ
         (vecDoubleDualIsoConcrete k V).hom.hom.hom
  have hW : (vecDoubleDualIsoConcrete k W).hom.hom.hom = Module.Dual.eval k W := by
    simp [vecDoubleDualIsoConcrete, LinearEquiv.toFGModuleCatIso_hom]; rfl
  have hV : (vecDoubleDualIsoConcrete k V).hom.hom.hom = Module.Dual.eval k V := by
    simp [vecDoubleDualIsoConcrete, LinearEquiv.toFGModuleCatIso_hom]; rfl
  rw [hW, hV]
  have hram : (rightAdjointMate (rightAdjointMate f)).hom.hom =
      (rightAdjointMate f).hom.hom.dualMap :=
    FGModuleCat.rightAdjointMate_hom_eq_dualMap k (rightAdjointMate f)
  have hram1 : (rightAdjointMate f).hom.hom = f.hom.hom.dualMap :=
    FGModuleCat.rightAdjointMate_hom_eq_dualMap k f
  rw [hram, hram1]
  apply LinearMap.ext; intro v
  apply LinearMap.ext; intro ψ
  rfl

/-- Monoidality of the concrete double-dual isomorphism: it factors the iso
`(V ⊗ W) ≅ ((V ⊗ W)*)*` through the iso `V ≅ (V*)*` tensored with `W ≅ (W*)*`,
followed by the tensor-coherence iso. -/
lemma vecDoubleDualIsoConcrete_monoidality (V W : FGModuleCat.{u} k) :
    (vecDoubleDualIsoConcrete k (V ⊗ W)).hom =
      ((vecDoubleDualIsoConcrete k V).hom ⊗ₘ (vecDoubleDualIsoConcrete k W).hom) ≫
        (vecTensorCoherenceIsoConcrete k V W).hom := by
  simp only [vecTensorCoherenceIsoConcrete, Iso.trans_hom, tensorIso_hom]
  rw [tensorHom_comp_tensorHom_assoc]
  simp [Iso.hom_inv_id]

set_option maxHeartbeats 800000 in
/-- The left quantum trace of the concrete double-dual isomorphism on the unit object
equals the identity of the unit — equivalently, `dim(𝟙) = 1` in `Vec_k`. -/
lemma vecDoubleDualIsoConcrete_dimUnit :
    leftQuantumTrace (FGModuleCat k) (vecDoubleDualIsoConcrete k (𝟙_ (FGModuleCat k))).hom =
    𝟙 (𝟙_ (FGModuleCat k)) := by

  have h1 : (leftQuantumTrace (FGModuleCat k)
      (vecDoubleDualIsoConcrete k (𝟙_ (FGModuleCat k))).hom).hom.hom 1 =
      (Module.finrank k (𝟙_ (FGModuleCat.{u} k)) : k) := by
    change (contractLeft k (Dual k (𝟙_ (FGModuleCat.{u} k))))
      (TensorProduct.map (Dual.eval k (𝟙_ (FGModuleCat.{u} k))) LinearMap.id
        (coevaluation k (𝟙_ (FGModuleCat.{u} k)) 1)) = _
    rw [coevaluation_apply_one]
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, contractLeft_apply,
      Dual.eval_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
      Finset.sum_const, Nat.smul_one_eq_cast]
    congr 1
    rw [Finset.card_univ]
    exact (Module.finrank_eq_card_basis (Basis.ofVectorSpace k (𝟙_ (FGModuleCat.{u} k)))).symm

  have h2 : Module.finrank k ↥(𝟙_ (FGModuleCat.{u} k)) = 1 := Module.finrank_self k
  have h3 : (leftQuantumTrace (FGModuleCat k)
      (vecDoubleDualIsoConcrete k (𝟙_ (FGModuleCat k))).hom).hom.hom 1 = (1 : k) := by
    rw [h1, h2, Nat.cast_one]

  exact InducedCategory.Hom.ext (ModuleCat.Hom.ext (LinearMap.ext_ring h3))

end FixDiamond
end
