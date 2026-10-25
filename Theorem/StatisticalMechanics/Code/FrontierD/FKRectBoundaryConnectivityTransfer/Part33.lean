/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part35
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


@[simp] theorem finFunctionConsEquiv_fst
    {n : Nat} {A : Type*} (f : Fin (n + 1) -> A) :
    (finFunctionConsEquiv n A f).1 = f 0 := rfl

@[simp] theorem finFunctionConsEquiv_snd
    {n : Nat} {A : Type*} (f : Fin (n + 1) -> A) (i : Fin n) :
    (finFunctionConsEquiv n A f).2 i = f i.succ := rfl

@[simp] theorem finFunctionConsEquiv_symm_zero
    {n : Nat} {A : Type*} (a : A) (f : Fin n -> A) :
    (finFunctionConsEquiv n A).symm (a, f) 0 = a := rfl

@[simp] theorem finFunctionConsEquiv_symm_succ
    {n : Nat} {A : Type*} (a : A) (f : Fin n -> A) (i : Fin n) :
    (finFunctionConsEquiv n A).symm (a, f) i.succ = f i := rfl


end
end StatMech.FrontierD
