/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_35_6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
set_option maxHeartbeats 800000


noncomputable section

open CategoryTheory TensorCategories

universe w

/-- Reconstruction data for part (i) of Theorem 1.35.6: bundles a finite-dimensional
quasi-bialgebra `H` equipped with an antipode together with the representation category
`Rep(H)` and the monoidal equivalence with `C`. -/
structure QuasiBialgebraAntipodeReconstructionData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RightRigidCategory C] where
  H : Type w
  [instRing : Ring H]
  [instAlgebra : Algebra k H]
  [instFiniteDimensional : FiniteDimensional k H]
  [instQuasiBialgebra : QuasiBialgebra k H]
  instAntipode : QuasiBialgebraAntipode k H
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  monoidalEquiv : MonoidalEquiv C RepH
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful

attribute [instance] QuasiBialgebraAntipodeReconstructionData.instRing
  QuasiBialgebraAntipodeReconstructionData.instAlgebra
  QuasiBialgebraAntipodeReconstructionData.instFiniteDimensional
  QuasiBialgebraAntipodeReconstructionData.instQuasiBialgebra
  QuasiBialgebraAntipodeReconstructionData.instCategoryRepH
  QuasiBialgebraAntipodeReconstructionData.instMonoidalRepH
  QuasiBialgebraAntipodeReconstructionData.instAbelianRepH

/-- Forward direction of Theorem 1.35.6(i): a finite abelian `k`-linear monoidal
category with right duals admitting a quasi-fiber functor yields a finite-dimensional
quasi-bialgebra with antipode. -/
structure QuasiBialgebraAntipodeRepData
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [FiniteDimensional k H]
    [QuasiBialgebra k H]
    (antipode : QuasiBialgebraAntipode k H) where
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  [instRightRigidRepH : @RightRigidCategory RepH instCategoryRepH instMonoidalRepH]
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful
  forgetPreservesMono : forgetRep.PreservesMonomorphisms
  forgetPreservesEpi : forgetRep.PreservesEpimorphisms

attribute [instance] QuasiBialgebraAntipodeRepData.instCategoryRepH
  QuasiBialgebraAntipodeRepData.instMonoidalRepH
  QuasiBialgebraAntipodeRepData.instAbelianRepH
  QuasiBialgebraAntipodeRepData.instRightRigidRepH

/-- Inverse direction of Theorem 1.35.6(i): a finite-dimensional quasi-bialgebra
with antipode yields the representation category with its forgetful functor. -/
structure QuasiHopfReconstructionData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C] where
  H : Type w
  [instRing : Ring H]
  [instAlgebra : Algebra k H]
  [instFiniteDimensional : FiniteDimensional k H]
  [instQuasiHopf : QuasiHopfAlgebra k H]
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  [instRigidRepH : @RigidCategory RepH instCategoryRepH instMonoidalRepH]
  monoidalEquiv : MonoidalEquiv C RepH
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful

attribute [instance] QuasiHopfReconstructionData.instRing
  QuasiHopfReconstructionData.instAlgebra
  QuasiHopfReconstructionData.instFiniteDimensional
  QuasiHopfReconstructionData.instQuasiHopf
  QuasiHopfReconstructionData.instCategoryRepH
  QuasiHopfReconstructionData.instMonoidalRepH
  QuasiHopfReconstructionData.instAbelianRepH
  QuasiHopfReconstructionData.instRigidRepH

/-- Forward direction of Theorem 1.35.6(ii): a finite tensor category admitting a
quasi-fiber functor produces a finite-dimensional quasi-Hopf algebra. -/
structure QuasiHopfRepData
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [FiniteDimensional k H]
    [QuasiHopfAlgebra k H] where
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  [instRigidRepH : @RigidCategory RepH instCategoryRepH instMonoidalRepH]
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful
  forgetPreservesMono : forgetRep.PreservesMonomorphisms
  forgetPreservesEpi : forgetRep.PreservesEpimorphisms

end
