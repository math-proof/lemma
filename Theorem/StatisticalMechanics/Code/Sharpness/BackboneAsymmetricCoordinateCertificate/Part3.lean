/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part5
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneP2CoordinateToggleObstruction

open FluxEdgeCopy

variable {D : Type*}


theorem BondwiseRunToggleCovariance.refl_of_outsideCut
    (E : BondwiseRunSpec V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (path : Finset (Copy G m))
    (hpath : SupportedInCut G m cut path)
    (hE : FluxEventOutsideCut G m cut (E.Event G)) :
    BondwiseRunToggleCovariance E E G m path := by
  intro T
  exact fluxEvent_toggle_iff G m cut (E.Event G) hE T path hpath


theorem BondwisePairEvent.toggle_iff_of_componentwise
    (left₁ left₂ right₁ right₂ : BondwiseRunSpec V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) (path : Finset (Copy G m))
    (h₁ : BondwiseRunToggleCovariance left₁ right₁ G m path)
    (h₂ : BondwiseRunToggleCovariance left₂ right₂ G m path)
    (T : Finset (Copy G m)) :
    BondwisePairEvent left₁ left₂ G m T <->
      BondwisePairEvent right₁ right₂ G m (T ∆ path) := by
  have hcompl : univ \ (T ∆ path) = (univ \ T) ∆ path :=
    compl_symmDiff G m T path
  constructor
  · rintro ⟨hleft₁, hleft₂⟩
    exact ⟨(h₁ T).mp hleft₁, by
      rw [hcompl]
      exact (h₂ (univ \ T)).mp hleft₂⟩
  · rintro ⟨hright₁, hright₂⟩
    exact ⟨(h₁ T).mpr hright₁, (h₂ (univ \ T)).mpr (by
      rw [hcompl] at hright₂
      exact hright₂)⟩


theorem BondwisePairEvent.toggle_iff_of_outsideCut
    (E₁ E₂ : BondwiseRunSpec V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (path : Finset (Copy G m))
    (hpath : SupportedInCut G m cut path)
    (h₁ : FluxEventOutsideCut G m cut (E₁.Event G))
    (h₂ : FluxEventOutsideCut G m cut (E₂.Event G))
    (T : Finset (Copy G m)) :
    BondwisePairEvent E₁ E₂ G m T <->
      BondwisePairEvent E₁ E₂ G m (T ∆ path) :=
  BondwisePairEvent.toggle_iff_of_componentwise E₁ E₂ E₁ E₂
    G m path
      (BondwiseRunToggleCovariance.refl_of_outsideCut
        E₁ G m cut path hpath h₁)
      (BondwiseRunToggleCovariance.refl_of_outsideCut
        E₂ G m cut path hpath h₂) T


end BackboneConcreteSelector
end
end StatMech.Sharpness
