/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part8
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem nonempty_pairedAlignedMixedLevelStep
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
    [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (S : Nat -> Finset V) (Sdual : Nat -> Finset W)
    (p pDual : Nat -> Real)
    (family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (familyDual : forall m,
      Edual.NormalBoundaryBandFamily muDual (Sdual m) (pDual m))
    (hp : Tendsto p atTop (nhds 1))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
    (previousScale previousConnector : Nat)
    {scoreEpsilon mergeEpsilon : Real}
    (hscoreEpsilon : 0 < scoreEpsilon)
    (hmergeEpsilon : 0 < mergeEpsilon) :
    Nonempty (PairedAlignedMixedLevelStep E Edual mu muDual
      S Sdual p pDual family familyDual
      verticalRequirement horizontalRequirement previousScale
      previousConnector scoreEpsilon mergeEpsilon) := by
  have hpEventually : ∀ᶠ m in atTop,
      1 - scoreEpsilon < p m :=
    (tendsto_order.1 hp).1 (1 - scoreEpsilon) (by linarith)
  have hpDualEventually : ∀ᶠ m in atTop,
      1 - scoreEpsilon < pDual m :=
    (tendsto_order.1 hpDual).1 (1 - scoreEpsilon) (by linarith)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 hpEventually
  obtain ⟨thresholdDual, hthresholdDual⟩ :=
    eventually_atTop.1 hpDualEventually
  let m := max previousScale (max threshold thresholdDual)
  have hm : previousScale <= m := Nat.le_max_left _ _
  have hpm : 1 - scoreEpsilon < p m :=
    hthreshold m ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have hpmDual : 1 - scoreEpsilon < pDual m :=
    hthresholdDual m
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  let schedule := Classical.choice
    (exists_pairedAlignedMarginSchedule E Edual
      (family m) (familyDual m)
      (verticalRequirement m) (horizontalRequirement m))
  let mixed := Classical.choice
    (exists_pairedMixedBoundaryScores E Edual mu muDual hTI hTIDual
      (family m) (familyDual m) schedule 0)
  let rotated := Classical.choice
    (exists_pairedRotatedMixedBoundaryScores E Edual mu muDual hTI hTIDual
      (family m) (familyDual m) schedule 0)
  obtain ⟨nextConnector, hconnector, hPV, hPH, hDV, hDH⟩ :=
    exists_pairedCommonBoundaryPairMergeRadius P Pdual mu muDual
      hunique huniqueDual
      mixed.primalBottomSource mixed.primalTopSource
      mixed.primalLeftSource mixed.primalRightSource
      mixed.dualBottomSource mixed.dualTopSource
      mixed.dualLeftSource mixed.dualRightSource
      previousConnector hmergeEpsilon
  exact ⟨{
    scale := m
    scale_ge := hm
    primal_threshold_gt := hpm
    dual_threshold_gt := hpmDual
    schedule := schedule
    mixed := mixed
    rotated := rotated
    nextConnector := nextConnector
    connector_mono := hconnector
    primalVerticalMerge := hPV
    primalHorizontalMerge := hPH
    dualVerticalMerge := hDV
    dualHorizontalMerge := hDH }⟩


theorem exists_recursivePairedAlignedMixedLevelSteps
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
    [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (S : Nat -> Finset V) (Sdual : Nat -> Finset W)
    (p pDual : Nat -> Real)
    (family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (familyDual : forall m,
      Edual.NormalBoundaryBandFamily muDual (Sdual m) (pDual m))
    (hp : Tendsto p atTop (nhds 1))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
    (scoreEpsilon mergeEpsilon : Nat -> Real)
    (hscoreEpsilon : forall n, 0 < scoreEpsilon n)
    (hmergeEpsilon : forall n, 0 < mergeEpsilon n) :
    exists state : Nat -> Nat × Nat,
      exists steps : forall n, PairedAlignedMixedLevelStep
        E Edual mu muDual S Sdual p pDual family familyDual
        verticalRequirement horizontalRequirement
        (state n).1 (state n).2 (scoreEpsilon n) (mergeEpsilon n),
      state 0 = (0, 0) /\
      forall n, state (n + 1) =
        ((steps n).scale + 1, (steps n).nextConnector) := by
  let chooseStep (n : Nat) (state : Nat × Nat) := Classical.choice
    (nonempty_pairedAlignedMixedLevelStep E Edual mu muDual hTI hTIDual
      hunique huniqueDual S Sdual p pDual family familyDual hp hpDual
      verticalRequirement horizontalRequirement state.1 state.2
      (hscoreEpsilon n) (hmergeEpsilon n))
  let state : Nat -> Nat × Nat := fun n =>
    Nat.rec (0, 0) (fun n previous =>
      let step := chooseStep n previous
      (step.scale + 1, step.nextConnector)) n
  let steps := fun n => chooseStep n (state n)
  refine ⟨state, steps, rfl, ?_⟩
  intro n
  simp only [state, steps]


theorem exists_recursivePairedAlignedMixedLevelSteps_with_limits
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
    [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (S : Nat -> Finset V) (Sdual : Nat -> Finset W)
    (p pDual : Nat -> Real)
    (family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (familyDual : forall m,
      Edual.NormalBoundaryBandFamily muDual (Sdual m) (pDual m))
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall m, p m <= 1)
    (hpDual : Tendsto pDual atTop (nhds 1))
    (hpDual_le : forall m, pDual m <= 1)
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat) :
    let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
    exists state : Nat -> Nat × Nat,
      exists steps : forall n, PairedAlignedMixedLevelStep
        E Edual mu muDual S Sdual p pDual family familyDual
        verticalRequirement horizontalRequirement
        (state n).1 (state n).2 (epsilon n) (epsilon n),
      state 0 = (0, 0) /\
      (forall n, state (n + 1) =
        ((steps n).scale + 1, (steps n).nextConnector)) /\
      Tendsto (fun n => (steps n).scale) atTop atTop /\
      Tendsto (fun n => p (steps n).scale) atTop (nhds 1) /\
      Tendsto (fun n => pDual (steps n).scale) atTop (nhds 1) /\
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion
        (steps n).mixed.primalBottomSource
        (steps n).mixed.primalTopSource (steps n).nextConnector))
        atTop (nhds 0) /\
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion
        (steps n).mixed.primalLeftSource
        (steps n).mixed.primalRightSource (steps n).nextConnector))
        atTop (nhds 0) /\
      Tendsto (fun n => muDual.real (Pdual.pairMergeErrorUnion
        (steps n).mixed.dualBottomSource
        (steps n).mixed.dualTopSource (steps n).nextConnector))
        atTop (nhds 0) /\
      Tendsto (fun n => muDual.real (Pdual.pairMergeErrorUnion
        (steps n).mixed.dualLeftSource
        (steps n).mixed.dualRightSource (steps n).nextConnector))
        atTop (nhds 0) := by
  dsimp only
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  obtain ⟨state, steps, hstate0, hstateSucc⟩ :=
    exists_recursivePairedAlignedMixedLevelSteps E Edual mu muDual
      hTI hTIDual hunique huniqueDual S Sdual p pDual family familyDual
      hp hpDual verticalRequirement horizontalRequirement
      epsilon epsilon hepsilon hepsilon
  have hstateCofinal : forall n, n <= (state n).1 := by
    intro n
    induction n with
    | zero => simp [hstate0]
    | succ n ih =>
        rw [hstateSucc n]
        exact Nat.succ_le_succ (ih.trans (steps n).scale_ge)
  have hscaleCofinal : forall n, n <= (steps n).scale := fun n =>
    (hstateCofinal n).trans (steps n).scale_ge
  have hscaleTop : Tendsto (fun n => (steps n).scale) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hscaleCofinal n)
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    simpa only [epsilon] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hlower : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  have hpStep : Tendsto (fun n => p (steps n).scale)
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (steps n).primal_threshold_gt)
      (fun n => hp_le (steps n).scale)
  have hpDualStep : Tendsto (fun n => pDual (steps n).scale)
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (steps n).dual_threshold_gt)
      (fun n => hpDual_le (steps n).scale)
  have hPV := squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => le_of_lt (steps n).primalVerticalMerge) hepsilonZero
  have hPH := squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => le_of_lt (steps n).primalHorizontalMerge) hepsilonZero
  have hDV := squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => le_of_lt (steps n).dualVerticalMerge) hepsilonZero
  have hDH := squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => le_of_lt (steps n).dualHorizontalMerge) hepsilonZero
  exact ⟨state, steps, hstate0, hstateSucc, hscaleTop, hpStep, hpDualStep,
    hPV, hPH, hDV, hDH⟩


end StatMech.FK.PeriodicPlanar
