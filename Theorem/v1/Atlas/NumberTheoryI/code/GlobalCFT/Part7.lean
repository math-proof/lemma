module
public import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Ideles
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.IdeleNorm
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Cor227
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Ch22NormGroup
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Prop2219
public import Def.v1.Atlas.NumberTheoryI.code.Ideles.Part3
public import Def.v1.Atlas.NumberTheoryI.code.IdeleNorm.Part4
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Theorem.v1.Atlas.NumberTheoryI.code.Cor227.Part2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Chapter3.FiniteApproximation
public import Theorem.v1.Atlas.NumberTheoryI.code.Ch22NormGroup.Part4
public import Def.v1.Atlas.NumberTheoryI.code.Prop2219.Part2
public import Structure.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

open Ideles

attribute [instance] GlobalArtinMap.instPreorder
  GlobalArtinMap.instFintype
  GlobalArtinMap.instCommGroup
  GlobalArtinMap.galAb_group
  GlobalArtinMap.galAb_topologicalSpace
  GlobalArtinMap.galAb_topologicalGroup
  GlobalArtinMap.galAb_compactSpace

theorem theorem_28_4_principal_in_ker {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) :
    principalIdeles K ≤ MonoidHom.ker θ.artinHom :=
  θ.principalInKer

end
