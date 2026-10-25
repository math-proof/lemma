/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TannakaReconstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.Tannaka
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Def.v1.Atlas.TensorCategories.code.TannakaReconstruction.Part2
set_option maxHeartbeats 800000

open CategoryTheory

universe u v w


noncomputable section

variable (k : Type u) [CommRing k] (A : Type u) [Ring A] [Algebra k A]

/-- A bialgebra equivalence between two `k`-bialgebras `A` and `B`: an algebra equivalence
which additionally preserves the comultiplication and the counit. -/
structure BialgebraEquiv (k : Type w) [CommSemiring k]
    (A : Type w) [Semiring A] [Bialgebra k A]
    (B : Type w) [Semiring B] [Bialgebra k B] extends A ≃ₐ[k] B where
  preserves_comul : ∀ a : A,
    Coalgebra.comul (R := k) (toAlgEquiv a) =
      TensorProduct.map toAlgEquiv.toLinearMap toAlgEquiv.toLinearMap (Coalgebra.comul (R := k) a)
  preserves_counit : ∀ a : A,
    Coalgebra.counit (R := k) (toAlgEquiv a) = Coalgebra.counit (R := k) a

/-- A bundled monoidal equivalence between monoidal categories `C` and `D`: an underlying
equivalence of categories together with monoidal structures on both directions. -/
structure MonoidalEquiv
    (C : Type*) [Category C] [MonoidalCategory C]
    (D : Type*) [Category D] [MonoidalCategory D] where
  equiv : C ≌ D
  functorMonoidal : equiv.functor.Monoidal
  inverseMonoidal : equiv.inverse.Monoidal

/-- Data witnessing the categorical part of Tannaka reconstruction (Theorem 1.23.1):
a coalgebra `H` together with an equivalence between `C` and the category of `H`-comodules
compatible with the fiber functor `F`. -/
structure TannakaReconstructionData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [Abelian C] [Linear k C]
    (F : C ⥤ ModuleCat.{w} k)
    [hFaithful : F.Faithful]
    [hExact : F.PreservesMonomorphisms] [hExact' : F.PreservesEpimorphisms] where
  H : Type w
  [instAddCommGroup : AddCommGroup H]
  [instModule : Module k H]
  [instCoalgebra : Coalgebra k H]
  ComodCat : Type (w+1)
  [instCategoryComod : Category.{w} ComodCat]
  [instAbelianComod : Abelian ComodCat]
  equiv : C ≌ ComodCat
  forgetComod : ComodCat ⥤ ModuleCat.{w} k
  forgetFaithful : forgetComod.Faithful
  compatF : F ≅ equiv.functor ⋙ forgetComod

attribute [instance] TannakaReconstructionData.instAddCommGroup
  TannakaReconstructionData.instModule
  TannakaReconstructionData.instCoalgebra
  TannakaReconstructionData.instCategoryComod
  TannakaReconstructionData.instAbelianComod

/-- Theorem 1.23.1: an exact faithful functor `F : C → Vec` defines an equivalence between
`C` and the category of finite-dimensional right comodules over `Coend(F)`. -/
structure MonoidalTannakaData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] where
  H : Type w
  [instRingH : Ring H]
  [instAlgebraH : Algebra k H]
  [instBialgebraH : Bialgebra k H]
  ComodCat : Type (w+1)
  [instCategoryComod : Category.{w} ComodCat]
  [instMonoidalComod : MonoidalCategory ComodCat]
  [instAbelianComod : Abelian ComodCat]
  monoidalEquiv : MonoidalEquiv C ComodCat
  forgetComod : ComodCat ⥤ ModuleCat.{w} k
  forgetFaithful : forgetComod.Faithful

attribute [instance] MonoidalTannakaData.instRingH
  MonoidalTannakaData.instAlgebraH
  MonoidalTannakaData.instBialgebraH
  MonoidalTannakaData.instCategoryComod
  MonoidalTannakaData.instMonoidalComod
  MonoidalTannakaData.instAbelianComod

/-- Theorem 1.23.2 (part 2): for `C` with right duals, the reconstructed bialgebra admits
an antipode and is a Hopf algebra, with the comodule category inheriting right rigidity. -/
structure TannakaWithAntipodeData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RightRigidCategory C] extends MonoidalTannakaData k C where
  instRightRigid : @RightRigidCategory ComodCat instCategoryComod instMonoidalComod
  instHopfAlgebra : HopfAlgebra k H

/-- Theorem 1.23.2 (part 3): for a rigid `C` (a tensor category), the reconstructed
Hopf algebra has bijective antipode and the equivalence is one of rigid monoidal categories. -/
structure TannakaHopfData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C] extends MonoidalTannakaData k C where
  instRigid : @RigidCategory ComodCat instCategoryComod instMonoidalComod
  instHopfAlgebra : HopfAlgebra k H
  antipodeBijective : Function.Bijective
    (@HopfAlgebraStruct.antipode k H _ _ instHopfAlgebra.toHopfAlgebraStruct)

/-- Theorem 1.23.2 (bialgebra case): a fiber functor on a monoidal abelian `k`-linear
category `C` reconstructs a `k`-bialgebra `H` with `C` monoidally equivalent to `H`-comodules. -/
structure FiniteTannakaHopfData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C] where
  H : Type w
  [instRingH : Ring H]
  [instAlgebraH : Algebra k H]
  [instHopfAlgebraH : HopfAlgebra k H]
  [instFiniteDimensionalH : FiniteDimensional k H]
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  [instRigidRepH : @RigidCategory RepH instCategoryRepH instMonoidalRepH]
  monoidalEquiv : MonoidalEquiv C RepH
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful

attribute [instance] FiniteTannakaHopfData.instRingH
  FiniteTannakaHopfData.instAlgebraH
  FiniteTannakaHopfData.instHopfAlgebraH
  FiniteTannakaHopfData.instFiniteDimensionalH
  FiniteTannakaHopfData.instCategoryRepH
  FiniteTannakaHopfData.instMonoidalRepH
  FiniteTannakaHopfData.instAbelianRepH
  FiniteTannakaHopfData.instRigidRepH

/-- In Tannaka reconstruction, the Hopf algebra `H` obtained from a finite tensor category `C`
with fiber functor is automatically finite-dimensional over `k`. -/
structure HopfAlgebraRepData
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [HopfAlgebra k H] [FiniteDimensional k H] where
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  [instRigidRepH : @RigidCategory RepH instCategoryRepH instMonoidalRepH]
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful
  forgetPreservesMono : forgetRep.PreservesMonomorphisms
  forgetPreservesEpi : forgetRep.PreservesEpimorphisms
  forgetMonoidal : forgetRep.Monoidal

attribute [instance] HopfAlgebraRepData.instCategoryRepH
  HopfAlgebraRepData.instMonoidalRepH
  HopfAlgebraRepData.instAbelianRepH
  HopfAlgebraRepData.instRigidRepH

/-- Theorem 1.22.11 (inverse direction): from a finite-dimensional Hopf algebra `H`, produce
the representation category `Rep(H)` and the forgetful fiber functor to `ModuleCat k`. -/
structure BialgebraComoduleData
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [Bialgebra k H] where
  ComodCat : Type (w+1)
  [instCategoryComod : Category.{w} ComodCat]
  [instMonoidalComod : MonoidalCategory ComodCat]
  [instAbelianComod : Abelian ComodCat]
  forgetComod : ComodCat ⥤ ModuleCat.{w} k
  forgetFaithful : forgetComod.Faithful
  forgetPreservesMono : forgetComod.PreservesMonomorphisms
  forgetPreservesEpi : forgetComod.PreservesEpimorphisms
  forgetMonoidal : forgetComod.Monoidal

attribute [instance] BialgebraComoduleData.instCategoryComod
  BialgebraComoduleData.instMonoidalComod
  BialgebraComoduleData.instAbelianComod

/-- Theorem 1.23.2 (inverse direction, bialgebra case): from a `k`-bialgebra `H`, produce the
monoidal abelian category of `H`-comodules together with its forgetful fiber functor. -/
structure QuasiFiberReconstructionData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (QF : QuasiFiberFunctor k C)
    (hNorm : QF.IsNormalized) where
  H : Type w
  [instRing : Ring H]
  [instAlgebra : Algebra k H]
  [instFiniteDimensional : FiniteDimensional k H]
  [instQuasiBialgebra : QuasiBialgebra k H]

end
