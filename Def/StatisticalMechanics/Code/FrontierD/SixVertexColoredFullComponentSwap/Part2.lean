/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredVertexCrossFineRowProfile
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredFullComponentSwap


namespace StatMech.FrontierD

noncomputable section

def FKColoredFullSwapBondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool) : Prop :=
  forall d : FKMedialDart T,
    mask d.1 ≠ mask (fkMedialBondMate T d).1 ->
      (source false).color d = (source true).color d


def fkColoredFullSwapTarget
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask) :
    FKColoredLoopPairingPair T := fun layer =>
  { pairing := fun v =>
      if mask v then (source (!layer)).pairing v
      else (source layer).pairing v
    color := fun d =>
      if mask d.1 then (source (!layer)).color d
      else (source layer).color d
    color_localMate := by
      rintro ⟨v, side⟩
      by_cases hm : mask v
      · simp only [hm, if_true, fkMedialLocalMate_eq_localSideMate]
        simpa only [fkMedialLocalMate_eq_localSideMate] using
          (source (!layer)).color_localMate (v, side)
      · simp only [hm, if_false, fkMedialLocalMate_eq_localSideMate]
        simpa only [fkMedialLocalMate_eq_localSideMate] using
          (source layer).color_localMate (v, side)
    color_bondMate := by
      intro d
      by_cases hd : mask d.1 <;>
        by_cases hm : mask (fkMedialBondMate T d).1
      · simp only [hd, hm, if_true]
        exact (source (!layer)).color_bondMate d
      · have hcross := hbond d (by simp [hd, hm])
        simp only [hd, hm, if_true, if_false]
        rw [(source layer).color_bondMate d]
        cases layer
        · simpa using hcross
        · simpa using hcross.symm
      · have hcross := hbond d (by simp [hd, hm])
        simp only [hd, hm, if_true, if_false]
        rw [(source (!layer)).color_bondMate d]
        cases layer
        · simpa using hcross.symm
        · simpa using hcross
      · simp only [hd, hm, if_false]
        exact (source layer).color_bondMate d }

end
end StatMech.FrontierD
