/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration.Part6
import Def.StatisticalMechanics.Code.Sharpness.BackbonePartialP2Reindex
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneLabeledSwitching

open FluxEdgeCopy

open RandomCurrent

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem rawSourcePairFiberMass_eq_labeled
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R] :
    rawSourcePairFiberMass G beta J m A Q R =
      labeledSourcePairFiberMass G beta J m A Q R := by
  classical
  rw [show rawSourcePairFiberMass G beta J m A Q R =
      ∑ K : {p : G.edgeFinset -> Nat // p <= m},
        if sources G (ofEdgeFun G K.1) = A ∧ Q K.1 ∧
            R (fun e => m e - K.1 e) then
          rawSplitWeight G beta J m K else 0 by
    unfold rawSourcePairFiberMass rawPairFiberMass
    apply Finset.sum_congr rfl
    intro K _
    simp only [and_assoc]]
  rw [rawPredicateMass_eq_labeled G beta J m
    (fun k => sources G (ofEdgeFun G k) = A ∧ Q k ∧
      R (fun e => m e - k e))]
  unfold labeledSourcePairFiberMass
  have hsubtype :
      (∑ S : Finset (FluxEdgeCopy.Copy G m),
        if RandomCurrent.sources (endsM G m) S = A ∧
            Q (profileFlux G m S) ∧
            R (profileFlux G m (univ \ S)) then
          labeledWeight G beta J m S else 0) =
        ∑ S : Fiber G m A (fun S =>
            Q (profileFlux G m S) ∧
              R (profileFlux G m (univ \ S))),
          labeledWeight G beta J m S.1 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro S
    simp
  rw [← hsubtype]
  apply Finset.sum_congr rfl
  intro S _
  rw [FluxEdgeCopy.sources_eq, FluxEdgeCopy.profileFlux_compl]


theorem rawSourcePairFiberMass_eq_of_labeledToggle
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (htransport : ∀ S,
      (Q₁ (profileFlux G m S) ∧
          R₁ (profileFlux G m (univ \ S))) <->
        (Q₂ (profileFlux G m (S ∆ P)) ∧
          R₂ (profileFlux G m (univ \ (S ∆ P))))) :
    rawSourcePairFiberMass G beta J m A Q₁ R₁ =
      rawSourcePairFiberMass G beta J m (A ∆ C) Q₂ R₂ := by
  rw [rawSourcePairFiberMass_eq_labeled G beta J m A Q₁ R₁,
    rawSourcePairFiberMass_eq_labeled G beta J m (A ∆ C) Q₂ R₂]
  exact sum_labeledWeight_toggle G beta J m A C P hPsrc
    (fun S => Q₁ (profileFlux G m S) ∧
      R₁ (profileFlux G m (univ \ S)))
    (fun S => Q₂ (profileFlux G m S) ∧
      R₂ (profileFlux G m (univ \ S))) htransport

end BackboneLabeledSwitching

namespace BackboneDeterminedCutSwitching

open FluxEdgeCopy

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem compl_symmDiff (m : G.edgeFinset -> Nat)
    (S P : Finset (FluxEdgeCopy.Copy G m)) :
    univ \ (S ∆ P) = (univ \ S) ∆ P := by
  classical
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_symmDiff]
  tauto


theorem pairTransport_of_fluxEventsOutsideCut
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    (hQ : FluxEventOutsideCut G m cut Q)
    (hR : FluxEventOutsideCut G m cut R)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hP : SupportedInCut G m cut P)
    (S : Finset (FluxEdgeCopy.Copy G m)) :
    (Q (profileFlux G m S) ∧
        R (profileFlux G m (univ \ S))) <->
      (Q (profileFlux G m (S ∆ P)) ∧
        R (profileFlux G m (univ \ (S ∆ P)))) := by
  have hQt := fluxEvent_toggle_iff G m cut Q hQ S P hP
  have hRt := fluxEvent_toggle_iff G m cut R hR (univ \ S) P hP
  rw [compl_symmDiff G m S P]
  exact and_congr hQt hRt


theorem rawSourcePairFiberMass_eq_of_determinedCutToggle
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (cut : Set (Sym2 V))
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (hPcut : SupportedInCut G m cut P)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R]
    (hQ : FluxEventOutsideCut G m cut Q)
    (hR : FluxEventOutsideCut G m cut R) :
    BackboneLabeledSwitching.rawSourcePairFiberMass
        G beta J m A Q R =
      BackboneLabeledSwitching.rawSourcePairFiberMass
        G beta J m (A ∆ C) Q R := by
  apply BackboneLabeledSwitching.rawSourcePairFiberMass_eq_of_labeledToggle
    G beta J m A C P hPsrc Q R Q R
  exact pairTransport_of_fluxEventsOutsideCut G m cut Q R hQ hR P hPcut

end BackboneDeterminedCutSwitching
end
end StatMech.Sharpness
