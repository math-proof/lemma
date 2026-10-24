/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_21_3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction

set_option maxHeartbeats 400000

open CategoryTheory

universe u

/-- Data reconstructing a finite-dimensional bialgebra `H` over `k` from a finite
abelian `k`-linear monoidal category `C` equipped with a fiber functor.
Bundles the bialgebra `H` together with its ring, algebra, bialgebra and
finite-dimensionality instances. -/
structure BialgebraReconstructionData
    (k : Type u) [Field k]
    (C : Type (u+1)) [Category.{u} C] [MonoidalCategory C] [Abelian C] where
  H : Type u
  [instRing : Ring H]
  [instAlgebra : Algebra k H]
  [instBialgebra : Bialgebra k H]
  [instFiniteDimensional : FiniteDimensional k H]

attribute [instance] BialgebraReconstructionData.instRing
  BialgebraReconstructionData.instAlgebra
  BialgebraReconstructionData.instBialgebra
  BialgebraReconstructionData.instFiniteDimensional

/-- Data reconstructing the representation category `Rep(H)` of a finite-dimensional
bialgebra `H` over `k`, including its abelian and monoidal structure together with
the forgetful functor `Rep(H) ⥤ ModuleCat k` and its faithfulness/monoidality. -/
structure RepresentationReconstructionData
    (k : Type u) [Field k]
    (H : Type u) [Ring H] [Algebra k H] [Bialgebra k H] [FiniteDimensional k H] where
  RepCat : Type (u+1)
  [instCategoryRep : Category.{u} RepCat]
  [instMonoidalRep : MonoidalCategory RepCat]
  [instAbelianRep : Abelian RepCat]
  forget : RepCat ⥤ ModuleCat.{u} k
  forgetFaithful : forget.Faithful
  forgetMonoidal : forget.Monoidal

attribute [instance] RepresentationReconstructionData.instCategoryRep
  RepresentationReconstructionData.instMonoidalRep
  RepresentationReconstructionData.instAbelianRep

/-- Forward direction of Theorem 1.21.3: given a finite abelian `k`-linear monoidal
category `C` with a fiber functor `F : C ⥤ ModuleCat k`, there exists a
reconstructed finite-dimensional bialgebra `H = End(F)`. -/
