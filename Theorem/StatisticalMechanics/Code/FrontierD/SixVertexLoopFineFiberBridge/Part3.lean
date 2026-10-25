/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFineFiberBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopDecoratedUnitTransfer
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLoopFineFiberBridge.Part2


namespace StatMech.FrontierD

noncomputable section

theorem loopFineProfileFibers_of_relationEdgeDegree
    {T : EvenTorus}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (related : forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      SixVertexLoopDecoratedPairFineProfileFiber
          T sourceLeft sourceRight profile ->
        SixVertexLoopDecoratedPairFineProfileFiber
          T targetLeft targetRight profile -> Prop)
    (hne : forall profile source,
      (Finset.univ.filter (related profile source)).Nonempty)
    (hdegree : forall profile source target,
      related profile source target ->
        (Finset.univ.filter fun otherSource =>
          related profile otherSource target).card <=
        (Finset.univ.filter (related profile source)).card) :
    SixVertexLoopDecoratedPairFineProfileFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  intro profile
  classical
  let sources : Finset (SixVertexLoopDecoratedPairFineProfileFiber
      T sourceLeft sourceRight profile) := Finset.univ
  have hHall := StatMech.FrontierA.card_le_bipartiteNeighbors_of_edgeDegree
    (related profile) sources
    (fun source _ => hne profile source)
    (fun source _ target hrelated =>
      hdegree profile source target hrelated)
  calc
    Fintype.card (SixVertexLoopDecoratedPairFineProfileFiber
        T sourceLeft sourceRight profile) = sources.card := by simp [sources]
    _ <= (Finset.univ.filter fun target =>
        ∃ source ∈ sources, related profile source target).card := hHall
    _ <= Fintype.card (SixVertexLoopDecoratedPairFineProfileFiber
        T targetLeft targetRight profile) := by
      simpa only [Finset.card_univ] using Finset.card_le_univ
        (Finset.univ.filter fun target =>
          ∃ source ∈ sources, related profile source target)


theorem rawFineProfile_of_loopFineProfileFibers
    {T : EvenTorus}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (hfiber : SixVertexLoopDecoratedPairFineProfileFiberDominates T
      sourceLeft sourceRight targetLeft targetRight) :
    forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        sourceLeft sourceRight targetLeft targetRight profile := by
  intro profile
  have hcard := hfiber profile
  rw [card_sixVertexLoopDecoratedPairFineProfileFiber,
    card_sixVertexLoopDecoratedPairFineProfileFiber] at hcard
  have hraw : sixVertexHorizontalFineRowProfileSectorPairSum
      T sourceLeft sourceRight profile <=
      sixVertexHorizontalFineRowProfileSectorPairSum
        T targetLeft targetRight profile := by
    exact Nat.le_of_mul_le_mul_right hcard (by positivity)
  unfold sixVertexHorizontalFineRowProfileSignedSum
  exact sub_nonneg.mpr (by exact_mod_cast hraw)


theorem rawFineProfile_of_loopRelationEdgeDegree
    {T : EvenTorus}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (related : forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      SixVertexLoopDecoratedPairFineProfileFiber
          T sourceLeft sourceRight profile ->
        SixVertexLoopDecoratedPairFineProfileFiber
          T targetLeft targetRight profile -> Prop)
    (hne : forall profile source,
      (Finset.univ.filter (related profile source)).Nonempty)
    (hdegree : forall profile source target,
      related profile source target ->
        (Finset.univ.filter fun otherSource =>
          related profile otherSource target).card <=
        (Finset.univ.filter (related profile source)).card) :
    forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        sourceLeft sourceRight targetLeft targetRight profile :=
  rawFineProfile_of_loopFineProfileFibers
    (loopFineProfileFibers_of_relationEdgeDegree related hne hdegree)


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopFineProfileFibers
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hfiber : SixVertexLoopDecoratedPairFineProfileFiberDominates T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile
    T middle hmiddle_pos hmiddle_lt
  exact rawFineProfile_of_loopFineProfileFibers hfiber

end
end StatMech.FrontierD
