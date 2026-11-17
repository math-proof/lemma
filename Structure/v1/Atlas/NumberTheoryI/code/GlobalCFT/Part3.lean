/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ideles
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdeleNorm
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor227
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ch22NormGroup
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Prop2219
public import Def.v1.Atlas.NumberTheoryI.code.Ideles.Part3
public import Def.v1.Atlas.NumberTheoryI.code.IdeleNorm.Part4
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Theorem.v1.Atlas.NumberTheoryI.code.Cor227.Part2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Chapter3.FiniteApproximation
public import Theorem.v1.Atlas.NumberTheoryI.code.Ch22NormGroup.Part4
public import Def.v1.Atlas.NumberTheoryI.code.Prop2219.Part2
public import Def.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part11


public noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

open Ideles

attribute [instance] GlobalArtinMap.instPreorder
  GlobalArtinMap.instFintype
  GlobalArtinMap.instCommGroup
  GlobalArtinMap.galAb_group
  GlobalArtinMap.galAb_topologicalSpace
  GlobalArtinMap.galAb_topologicalGroup
  GlobalArtinMap.galAb_compactSpace

structure GlobalArtinFunctoriality
    (θK : GlobalArtinMap K) (θL : GlobalArtinMap L) where
  transfer : θL.GalAb →* θK.GalAb
  transfer_continuous : Continuous transfer
  artinMap_comm : ∀ (a : IdeleGroup L),
    θK.artinHom (ideleNorm K L a) = transfer (θL.artinHom a)

end
