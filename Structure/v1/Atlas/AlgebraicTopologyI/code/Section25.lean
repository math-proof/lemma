/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.EilenbergZilber
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section25.Part2
open CategoryTheory MonoidalCategory Limits


public noncomputable section

namespace AcyclicModels

universe u v

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- An augmented chain-complex-valued functor: a functor $\mathcal{C} \to \mathrm{Ch}_*$
together with an augmentation $F_0 \to T$ to a target functor $T : \mathcal{C} \to \mathrm{Ab}$.
This is the input data on which the acyclic models theorem operates. -/
structure AugChainComplexFunctor (𝒞 : Type u) [Category.{v} 𝒞] where
  chainFun : 𝒞 ⥤ HomologicalComplex AddCommGrpCat.{v} (ComplexShape.down ℕ)
  target : 𝒞 ⥤ AddCommGrpCat.{v}
  augmentation :
    chainFun ⋙ HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.down ℕ) 0 ⟶ target

end AcyclicModels
end
