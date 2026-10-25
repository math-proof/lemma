/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Monoidal
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.Basic
import Theorem.v1.Atlas.AlgebraicTopologyI.code.EilenbergZilber
import Def.v1.Atlas.AlgebraicTopologyI.code.Section25.Part2
open CategoryTheory MonoidalCategory Limits


noncomputable section

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
