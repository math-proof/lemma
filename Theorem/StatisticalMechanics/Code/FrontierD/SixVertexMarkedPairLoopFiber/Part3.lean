/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part4
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem exists_injective_decoratedZero_of_loopReconnection
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hreconnect : SixVertexLoopDecoratedPairTotalCReconnection
      T lower middle upper) :
    exists matching : SixVertexMarkedDecoratedPair T lower upper 0 ->
        SixVertexMarkedDecoratedPair T middle middle 0,
      Function.Injective matching /\
        forall source,
          sixVertexMarkedDecoratedPairTotalC source =
            sixVertexMarkedDecoratedPairTotalC (matching source) := by
  obtain ⟨loopMatching, hinjective, htotal⟩ := hreconnect
  let sourceEquiv :=
    sixVertexMarkedDecoratedPairZeroEquivLoop T lower upper
  let targetEquiv :=
    sixVertexMarkedDecoratedPairZeroEquivLoop T middle middle
  let matching : SixVertexMarkedDecoratedPair T lower upper 0 ->
      SixVertexMarkedDecoratedPair T middle middle 0 :=
    fun source => targetEquiv.symm (loopMatching (sourceEquiv source))
  refine ⟨matching, ?_, ?_⟩
  · exact targetEquiv.symm.injective.comp
      (hinjective.comp sourceEquiv.injective)
  · intro source
    have h := htotal (sourceEquiv source)
    change sixVertexMarkedDecoratedPairTotalC source =
      sixVertexMarkedDecoratedPairTotalC
        (targetEquiv.symm (loopMatching (sourceEquiv source)))
    rw [← sixVertexMarkedDecoratedPairZeroEquivLoop_totalC
      T lower upper source,
      ← sixVertexMarkedDecoratedPairZeroEquivLoop_totalC
        T middle middle
        (targetEquiv.symm (loopMatching (sourceEquiv source)))]
    simpa [targetEquiv] using h


theorem configurationPairTotalCFiberDominates_of_loopReconnection
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hreconnect : SixVertexLoopDecoratedPairTotalCReconnection
      T lower middle upper) :
    SixVertexConfigurationPairTotalCFiberDominates
      T lower middle upper := by
  have hdecorated :
      SixVertexMarkedDecoratedPairTotalCFiberDominates
        T lower middle upper 0 :=
    (exists_injective_gradePreserving_iff_fiberCard
      (fun source : SixVertexMarkedDecoratedPair T lower upper 0 =>
        sixVertexMarkedDecoratedPairTotalC source)
      (fun target : SixVertexMarkedDecoratedPair T middle middle 0 =>
        sixVertexMarkedDecoratedPairTotalC target)).mp
      (exists_injective_decoratedZero_of_loopReconnection hreconnect)
  intro total
  have htotal := hdecorated total
  rw [card_sixVertexMarkedDecoratedPairTotalCFiber,
    card_sixVertexMarkedDecoratedPairTotalCFiber] at htotal
  simp only [Nat.sub_zero, Nat.choose_zero_right, mul_one] at htotal
  exact Nat.le_of_mul_le_mul_right htotal (pow_pos (by norm_num) total)


theorem configurationPairTotalCReconnection_of_loopReconnection
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hreconnect : SixVertexLoopDecoratedPairTotalCReconnection
      T lower middle upper) :
    SixVertexConfigurationPairTotalCReconnection T lower middle upper :=
  (configurationPairTotalCReconnection_iff_fiberDominates
    T lower middle upper).mpr
      (configurationPairTotalCFiberDominates_of_loopReconnection hreconnect)


end
end StatMech.FrontierD
