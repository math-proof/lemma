/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredVertexCrossFineRowProfile
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredFullComponentSwap.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkColoredFullSwapTarget_pairing
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask)
    (layer : Bool) (v : T.Vertex) :
    (fkColoredFullSwapTarget source mask hbond layer).pairing v =
      if mask v then (source (!layer)).pairing v
      else (source layer).pairing v := rfl

@[simp] theorem fkColoredFullSwapTarget_color
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask)
    (layer : Bool) (d : FKMedialDart T) :
    (fkColoredFullSwapTarget source mask hbond layer).color d =
      if mask d.1 then (source (!layer)).color d
      else (source layer).color d := rfl

@[simp] theorem fkColoredFullSwapTarget_horizontal
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask)
    (layer : Bool) (v : T.Vertex) :
    (fkColoredFullSwapTarget source mask hbond layer).arrows.horizontal v =
      if mask v then (source (!layer)).arrows.horizontal v
      else (source layer).arrows.horizontal v := by
  cases layer <;> by_cases hm : mask v <;>
    simp [FKColoredLoopPairing.arrows, FKColoredLoopPairing.incoming,
      fkColoredFullSwapTarget, hm]

@[simp] theorem fkColoredFullSwapTarget_vertical
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask)
    (layer : Bool) (v : T.Vertex) :
    (fkColoredFullSwapTarget source mask hbond layer).arrows.vertical v =
      if mask v then (source (!layer)).arrows.vertical v
      else (source layer).arrows.vertical v := by
  cases layer <;> by_cases hm : mask v <;>
    simp [FKColoredLoopPairing.arrows, FKColoredLoopPairing.incoming,
      fkColoredFullSwapTarget, hm]

theorem fkColoredFullSwapTarget_bondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask) :
    FKColoredFullSwapBondCoherent
      (fkColoredFullSwapTarget source mask hbond) mask := by
  intro d hmask
  have hsource := hbond d hmask
  by_cases hd : mask d.1 = true
  · simp [fkColoredFullSwapTarget_color, hd, hsource]
  · have hdfalse : mask d.1 = false := Bool.eq_false_of_not_eq_true hd
    simp [fkColoredFullSwapTarget_color, hdfalse, hsource]

@[simp] theorem fkColoredFullSwapTarget_involutive
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask) :
    fkColoredFullSwapTarget
        (fkColoredFullSwapTarget source mask hbond) mask
        (fkColoredFullSwapTarget_bondCoherent source mask hbond) = source := by
  funext layer
  apply FKColoredLoopPairing.ext
  · funext v
    by_cases hm : mask v <;> cases layer <;> simp [hm]
  · funext d
    by_cases hm : mask d.1 <;> cases layer <;> simp [hm]


end
end StatMech.FrontierD
