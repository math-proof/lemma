/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part9
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace BackboneTwoEdgeCycleObstruction

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneTwoEdgeBondProgram

open BackboneTwoEdgeBondToggle

open FluxEdgeCopy

attribute [simp] headEdge_ne_suffixEdge headEdge_ne_cycleEdge₀
  headEdge_ne_cycleEdge₁ headEdge_ne_cycleEdge₂
  suffixEdge_ne_cycleEdge₀ suffixEdge_ne_cycleEdge₁
  suffixEdge_ne_cycleEdge₂ cycleEdge₀_ne_cycleEdge₁
  cycleEdge₀_ne_cycleEdge₂ cycleEdge₁_ne_cycleEdge₂
  suffixEdge_ne_headEdge cycleEdge₀_ne_headEdge cycleEdge₁_ne_headEdge
  cycleEdge₂_ne_headEdge cycleEdge₀_ne_suffixEdge
  cycleEdge₁_ne_suffixEdge cycleEdge₂_ne_suffixEdge
  cycleEdge₁_ne_cycleEdge₀ cycleEdge₂_ne_cycleEdge₀
  cycleEdge₂_ne_cycleEdge₁


theorem oddCycleSplit_filter_cycle₀ :
    oddCycleSplit.filter
        (fun i : Copy domain.graph superposition => i.1 = cycleEdge₀) =
      {cycle₀Copy₀} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hedge⟩
    unfold oddCycleSplit at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases i with ⟨e, j⟩
    dsimp only at hedge hi ⊢
    subst e
    unfold cycle₀Copy₀
    rw [Sigma.mk.inj_iff]
    have hflux : oddCycleFlux cycleEdge₀ = 1 := oddCycleFlux_cycle₀
    rw [hflux] at hi
    have hj : j.val = 0 := by omega
    refine ⟨rfl, heq_of_eq ?_⟩
    exact Fin.ext hj
  · intro hi
    subst i
    constructor
    · unfold oddCycleSplit cycle₀Copy₀
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp
    · rfl

theorem filter_symmDiff
    (S T : Finset (Copy domain.graph superposition)) :
    (S ∆ T).filter (fun i => i.1 = cycleEdge₀) =
      S.filter (fun i => i.1 = cycleEdge₀) ∆
        T.filter (fun i => i.1 = cycleEdge₀) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_symmDiff]
  tauto

theorem odd_card_symmDiff_singleton_iff_not
    {A : Type*} [DecidableEq A] (S : Finset A) (a : A) :
    Odd #(S ∆ {a}) ↔ ¬ Odd #S := by
  by_cases ha : a ∈ S
  · have heq : S ∆ {a} = S.erase a := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton,
        Finset.mem_erase]
      by_cases hxa : x = a
      · subst x
        simp [ha]
      · simp [hxa]
    rw [heq, Finset.card_erase_of_mem ha]
    rw [Nat.odd_sub (Finset.card_pos.mpr ⟨a, ha⟩)]
    simp
  · have heq : S ∆ {a} = insert a S := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton,
        Finset.mem_insert]
      by_cases hxa : x = a
      · subst x
        simp [ha]
      · simp [hxa]
    rw [heq, Finset.card_insert_of_notMem ha]
    rw [Nat.odd_add]
    simp


theorem profile_cycle₀_odd_symmDiff_iff_not
    (T : Finset (Copy domain.graph superposition)) :
    Odd (profileFlux domain.graph superposition (T ∆ oddCycleSplit)
      cycleEdge₀) ↔
      ¬ Odd (profileFlux domain.graph superposition T cycleEdge₀) := by
  unfold profileFlux
  let A := T.filter (fun i : Copy domain.graph superposition =>
    i.1 = cycleEdge₀)
  have hset :
      (T ∆ oddCycleSplit).filter (fun i => i.1 = cycleEdge₀) =
        A ∆ {cycle₀Copy₀} := by
    dsimp only [A]
    rw [filter_symmDiff T oddCycleSplit, oddCycleSplit_filter_cycle₀]
    rfl
  change Odd #((T ∆ oddCycleSplit).filter
      (fun i => i.1 = cycleEdge₀)) ↔ ¬ Odd #A
  rw [hset]
  exact odd_card_symmDiff_singleton_iff_not A cycle₀Copy₀


@[simp] theorem profileFlux_empty :
    profileFlux domain.graph superposition
      (∅ : Finset (Copy domain.graph superposition)) = 0 := by
  funext e
  simp [profileFlux]
  rfl


theorem no_residualVacuum_suffix_covariance
    (path : Finset (Copy domain.graph superposition)) :
    ¬ BondwiseRunToggleCovariance
      (residualVacuumRunSpec domain
        (canonicalEdgeSegment domain.graph headEdge))
      ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).liftedResidualRunSpec
        domain (canonicalEdgeSegment domain.graph headEdge)
        [canonicalEdgeSegment domain.graph suffixEdge])
      domain.graph superposition path := by
  intro hcov
  have hvacuumZero :
      (residualVacuumRunSpec domain
        (canonicalEdgeSegment domain.graph headEdge)).Event
        domain.graph (profileFlux domain.graph superposition ∅) := by
    rw [profileFlux_empty]
    exact vacuum_zero domain headEdge
  have hsuffixPath := (hcov ∅).mp hvacuumZero
  have hsuffixPath' :
      ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).liftedResidualRunSpec
        domain (canonicalEdgeSegment domain.graph headEdge)
        [canonicalEdgeSegment domain.graph suffixEdge]).Event domain.graph
        (profileFlux domain.graph superposition path) := by
    have heq : (∅ : Finset (Copy domain.graph superposition)) ∆ path = path :=
      symmDiff_eq_right.mpr rfl
    rw [heq] at hsuffixPath
    exact hsuffixPath
  have hpathEven :
      ¬ Odd (profileFlux domain.graph superposition path cycleEdge₀) :=
    suffix_event_cycle₀_not_odd _ hsuffixPath'
  have hsuffixToggle := (hcov oddCycleSplit).mp (by
    rw [profileFlux_oddCycleSplit]
    exact oddCycle_vacuum_event)
  have htoggleOdd :
      Odd (profileFlux domain.graph superposition
        (oddCycleSplit ∆ path) cycleEdge₀) := by
    rw [symmDiff_comm]
    exact (profile_cycle₀_odd_symmDiff_iff_not path).mpr hpathEven
  exact (suffix_event_cycle₀_not_odd _ hsuffixToggle) htoggleOdd


theorem superposition_weight_pos
    (beta : Real) (J : Sym2 (Fin 6) → Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g) :
    0 < weight domain.graph beta J
      (ofEdgeFun domain.graph superposition) := by
  unfold weight
  refine Finset.prod_pos (fun g _ => ?_)
  exact div_pos (pow_pos (mul_pos hbeta (hJ g)) _)
    (by positivity)


theorem right_rawPairFiberMass_pos
    (beta : Real) (J : Sym2 (Fin 6) → Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g) :
    0 < rawSourcePairFiberMass domain.graph beta J superposition
      (((BackboneTwoEdgeBondProgram.selectorSpec
          (V := Fin 6)).toPartialSelector.sourceClass domain
          [canonicalEdgeSegment domain.graph headEdge,
            canonicalEdgeSegment domain.graph suffixEdge]) ∆
        stepToggleSource
          (BackboneTwoEdgeBondProgram.selectorSpec
            (V := Fin 6)).toPartialSelector domain
          (canonicalEdgeSegment domain.graph headEdge)
          [canonicalEdgeSegment domain.graph suffixEdge])
      (shb_ActiveSegmentFiber domain
        (canonicalEdgeSegment domain.graph headEdge) head_active)
      (liftedResidualFiber
        (BackboneTwoEdgeBondProgram.selectorSpec
          (V := Fin 6)).toPartialSelector domain
        (canonicalEdgeSegment domain.graph headEdge)
        [canonicalEdgeSegment domain.graph suffixEdge]) := by
  let S := (BackboneTwoEdgeBondProgram.selectorSpec (V := Fin 6)).toPartialSelector
  let s := canonicalEdgeSegment domain.graph headEdge
  let t := canonicalEdgeSegment domain.graph suffixEdge
  let word := [s, t]
  let A := S.sourceClass domain word ∆
    stepToggleSource S domain s [t]
  let Q := fun T : Finset (Copy domain.graph superposition) =>
    shb_ActiveSegmentFiber domain s head_active
        (profileFlux domain.graph superposition T) ∧
      liftedResidualFiber S domain s [t]
        (profileFlux domain.graph superposition (univ \ T))
  have hresidual : liftedResidualFiber S domain s [t] suffixEvenFlux := by
    apply ((BackboneTwoEdgeBondProgram.selectorSpec
      (V := Fin 6)).liftedResidualFiber_iff_liftedRunEvent
        domain s [t] suffixEvenFlux).mpr
    exact (BondwiseSegmentProgram.liftedResidualRunSpec_event
      (BackboneTwoEdgeBondProgram.program (V := Fin 6)) domain s [t]
      suffixEvenFlux).mp suffixEven_event
  have hsource : RandomCurrent.sources (endsM domain.graph superposition)
      headSplit = A := by
    calc
      RandomCurrent.sources (endsM domain.graph superposition) headSplit =
          sources domain.graph (ofEdgeFun domain.graph
            (profileFlux domain.graph superposition headSplit)) :=
        FluxEdgeCopy.sources_eq domain.graph superposition headSplit
      _ = sources domain.graph
          (ofEdgeFun domain.graph (unitFlux domain.graph headEdge)) := by
        rw [profileFlux_headSplit]
      _ = {s.1, s.2.1} := sources_unitFlux domain.graph headEdge
      _ = A := by
        simp [A, stepToggleSource, word]
  have hQ : Q headSplit := by
    constructor
    · rw [profileFlux_headSplit]
      exact activeSegmentFiber_unitFlux domain headEdge head_active
    · rw [profileFlux_headSplit_compl]
      exact hresidual
  let witness : Fiber domain.graph superposition A Q :=
    ⟨headSplit, hsource, hQ⟩
  change 0 < rawSourcePairFiberMass domain.graph beta J superposition A
    (shb_ActiveSegmentFiber domain s head_active)
    (liftedResidualFiber S domain s [t])
  rw [rawSourcePairFiberMass_eq_labeled]
  unfold labeledSourcePairFiberMass
  exact Finset.sum_pos
    (fun _ _ => superposition_weight_pos beta J hbeta hJ)
    ⟨witness, Finset.mem_univ witness⟩


theorem coordinatePairContributes
    (beta : Real) (J : Sym2 (Fin 6) → Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g) :
    CoordinatePairContributes
      (BackboneTwoEdgeBondProgram.selectorSpec
        (V := Fin 6)).toPartialSelector
      beta J domain (canonicalEdgeSegment domain.graph headEdge)
      [canonicalEdgeSegment domain.graph suffixEdge] head_active
      superposition := by
  exact Or.inr (ne_of_gt (right_rawPairFiberMass_pos beta J hbeta hJ))


theorem not_canonicalComponentwiseToggleExists
    (beta : Real) (J : Sym2 (Fin 6) → Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g) :
    ¬ (BackboneTwoEdgeBondProgram.selectorSpec
      (V := Fin 6)).CanonicalComponentwiseToggleExists
      beta J domain (canonicalEdgeSegment domain.graph headEdge)
      [canonicalEdgeSegment domain.graph suffixEdge] head_active := by
  intro htoggle
  obtain ⟨path, _, hresidual⟩ :=
    htoggle superposition (coordinatePairContributes beta J hbeta hJ)
  exact no_residualVacuum_suffix_covariance path hresidual

end BackboneTwoEdgeCycleObstruction
end
end StatMech.Sharpness
