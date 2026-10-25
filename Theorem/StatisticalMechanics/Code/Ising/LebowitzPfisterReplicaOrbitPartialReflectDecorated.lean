/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPartialReflectDecorated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSplitTag.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitTagReconstruction.Part4
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPartialReflectDecorated
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplica_cast_subtype_val
    {J : Type*} (F : J -> Type*) (P : ∀ j, F j -> Prop)
    {a b : J} (h : a = b) (x : {y : F a // P a y}) :
    (cast (congrArg (fun j => {y : F j // P j y}) h) x).1 =
      cast (congrArg F h) x.1 := by
  subst b
  rfl


end
end StatMech.Ising
