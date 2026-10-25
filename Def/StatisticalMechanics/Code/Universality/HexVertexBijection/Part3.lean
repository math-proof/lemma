/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection.Part4


namespace StatMech.Universality

open Complex

open Function

open HexWalk


variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


noncomputable def emptyEnumeration (a : ℂ) (h0 : ℤ) (v du : ℂ) :
    HexVertexEnumeration (fun _ => False) a h0 v du :=
  HexVertexEnumeration.empty (fun _ => False) a h0 v du
    (fun z => parafObservable_emptyRegion a h0 z _ _)


end StatMech.Universality
