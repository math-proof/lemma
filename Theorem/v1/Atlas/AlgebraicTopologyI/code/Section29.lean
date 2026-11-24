module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section27
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section27
public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section29.Part3
open DirectSum GradedMonoid
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace SingularCohomology

variable (R : Type) [CommRing R]

set_option maxHeartbeats 6400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The augmentation cocycle $\varepsilon$ is indeed a $0$-cocycle: its
coboundary vanishes, since for each $1$-simplex $\sigma$ both endpoints map to
$1 \in R$ and cancel. Used to lift $\varepsilon$ to a cohomology class. -/
lemma augmentationCocycle_coboundary_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X).d 1 0 ≫
      augmentationCocycle R X = 0 := by
  apply Sigma.hom_ext
  intro σ
  simp only [Limits.HasZeroMorphisms.comp_zero, ← Category.assoc, augmentationCocycle]
  simp only [singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.whiskeringLeft, Functor.postcompose₂]
  erw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, Preadditive.sum_comp,
    Preadditive.zsmul_comp]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    SimplicialObject.δ]
  erw [Sigma.ι_comp_map' _ _ σ, Sigma.ι_comp_map' _ _ σ]
  simp only [Category.id_comp, Sigma.ι_desc]
  simp [add_neg_cancel]

end SingularCohomology
end
