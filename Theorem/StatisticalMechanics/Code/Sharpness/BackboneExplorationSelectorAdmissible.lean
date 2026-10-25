/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelectorAdmissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationCutAdmissible.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible.Part2
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem shb_cutLocalSourceSelector_admissible
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (Aleft Aright : Finset V)
    (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop) :
    shb_LocalSourceSelectorAdmissible G P (Aleft ∆ Aright) Aleft Aright
      (shb_cutLocalSourceSelector G P Aleft Aright
        leftSelector rightSelector)
      leftSelector rightSelector := by
  classical
  intro a b
  have hab : shb_cutEquiv G P (shb_cutJoin G P (a, b)) = (a, b) :=
    (shb_cutEquiv G P).apply_symm_apply (a, b)
  constructor
  · rintro ⟨_, hselector⟩
    unfold shb_cutLocalSourceSelector at hselector
    dsimp only at hselector
    rw [hab] at hselector
    exact ⟨hselector.1, hselector.2⟩
  · rintro ⟨⟨hleftSource, hleft⟩, ⟨hrightSource, hright⟩⟩
    refine ⟨?_, ?_⟩
    · rw [shb_sources_cutJoin G P a b, hleftSource, hrightSource]
    · unfold shb_cutLocalSourceSelector
      dsimp only
      rw [hab]
      exact ⟨⟨hleftSource, hleft⟩, ⟨hrightSource, hright⟩⟩


theorem shb_cutLocalSourceSelectorMass_factor
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (Aleft Aright : Finset V)
    (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    [DecidablePred leftSelector]
    (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    [DecidablePred rightSelector] :
    shb_cutFullPredicateMass G beta J
        (fun m => sources G (ofEdgeFun G m) = Aleft ∆ Aright /\
          shb_cutLocalSourceSelector G P Aleft Aright
            leftSelector rightSelector m) =
      shb_cutLeftPredicateMass G beta J P
          (fun a => sources G (ofEdgeFun G (shb_cutLeft G P a)) = Aleft /\
            leftSelector a) *
        shb_cutRightPredicateMass G beta J P
          (fun b => sources G (ofEdgeFun G (shb_cutRight G P b)) = Aright /\
            rightSelector b) := by
  exact shb_localSourceSelectorMass_factor G beta J P
    (Aleft ∆ Aright) Aleft Aright
    (shb_cutLocalSourceSelector G P Aleft Aright leftSelector rightSelector)
    leftSelector rightSelector
    (shb_cutLocalSourceSelector_admissible G P Aleft Aright
      leftSelector rightSelector)


theorem shb_dynamicSegmentCutLocalSelector_admissible
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (Aleft Aright : Finset V)
    (leftSelector :
      ({e : d.graph.edgeFinset // shb_segmentCut d.graph s e} -> Nat) -> Prop)
    (rightSelector :
      ({e : d.graph.edgeFinset // Not (shb_segmentCut d.graph s e)} -> Nat) -> Prop) :
    shb_LocalSourceSelectorAdmissible d.graph (shb_segmentCut d.graph s)
      (Aleft ∆ Aright) Aleft Aright
      (shb_cutLocalSourceSelector d.graph (shb_segmentCut d.graph s)
        Aleft Aright leftSelector rightSelector)
      leftSelector rightSelector :=
  shb_cutLocalSourceSelector_admissible d.graph
    (shb_segmentCut d.graph s) Aleft Aright leftSelector rightSelector


end
end StatMech.Sharpness
