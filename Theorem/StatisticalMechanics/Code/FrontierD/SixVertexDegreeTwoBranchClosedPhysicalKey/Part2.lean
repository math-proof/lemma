/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoBranchClosed_unsynchronized_no_vertex_mask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (d : SixVertexOrientedDisagreementDart omega eta)
    (hunsync : ¬ sixVertexDegreeTwoBranchClosedSynchronizedAt homega heta
      hdegree middle homegaSector hetaSector hmiddle d)
    (mask : Bool) :
    (mask != sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree
        middle homegaSector hetaSector hmiddle (d, false)) = true \/
      (mask != sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree
        middle homegaSector hetaSector hmiddle (d, true)) = true := by
  unfold sixVertexDegreeTwoBranchClosedSynchronizedAt at hunsync
  cases hfalse : sixVertexDegreeTwoBranchClosedTransitionBit homega heta
      hdegree middle homegaSector hetaSector hmiddle (d, false) <;>
    cases htrue : sixVertexDegreeTwoBranchClosedTransitionBit homega heta
      hdegree middle homegaSector hetaSector hmiddle (d, true) <;>
    cases mask <;> simp_all


theorem sixVertexDegreeTwoBranchClosedExpandedRetieMask_misses_transition
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (d : SixVertexOrientedDisagreementDart omega eta)
    (hunsync : ¬ sixVertexDegreeTwoBranchClosedSynchronizedAt homega heta
      hdegree middle homegaSector hetaSector hmiddle d)
    (layer : Bool) :
    ∃ branch : Bool,
      (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree
          middle homegaSector hetaSector hmiddle layer d.1.1.1 !=
        sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree middle
          homegaSector hetaSector hmiddle (d, branch)) = true := by
  have hmismatch := sixVertexDegreeTwoBranchClosed_unsynchronized_no_vertex_mask
    homega heta hdegree middle homegaSector hetaSector hmiddle d hunsync
    (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer d.1.1.1)
  rcases hmismatch with hfalse | htrue
  · exact ⟨false, hfalse⟩
  · exact ⟨true, htrue⟩


theorem sixVertexDegreeTwoBranchClosedTransitionVertex_eq_bit_of_synchronized
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (d : SixVertexOrientedDisagreementDart omega eta)
    (hsync : sixVertexDegreeTwoBranchClosedSynchronizedAt homega heta hdegree
      middle homegaSector hetaSector hmiddle d) :
    sixVertexDegreeTwoBranchClosedTransitionVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle d.1.1.1 =
      sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree middle
        homegaSector hetaSector hmiddle (d, false) := by
  have hactive := sixVertexDisagreementDart_local_card_eq_two hdegree d.1
  let d0 := orientedDisagreementDartAtActiveVertex homega heta d.1.1.1 hactive
  have hd0 : d0 = d := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d0 d rfl
  unfold sixVertexDegreeTwoBranchClosedTransitionVertex
  rw [dif_pos hactive]
  dsimp only
  change orientedDisagreementDartAtActiveVertex homega heta d.1.1.1 hactive = d
    at hd0
  rw [hd0]
  unfold sixVertexDegreeTwoBranchClosedSynchronizedAt at hsync
  unfold sixVertexDegreeTwoBranchClosedTransitionBit at hsync ⊢
  rw [hsync, Bool.or_self]


end
end StatMech.FrontierD
