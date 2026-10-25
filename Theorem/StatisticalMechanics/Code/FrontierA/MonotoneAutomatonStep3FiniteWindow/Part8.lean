/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part7
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem contactOverlapPairs_card_le
    (i : (Finset (Site d) × Site d) × Site d) (D : ℕ)
    (hiDist : l1dist d i.1.2 i.2 = D) :
    (contactOverlapPairs i D).card ≤ (boxFinsetBK d D).card ^ 3 := by
  classical
  let B := (boxFinsetBK d D).card
  calc
    (contactOverlapPairs i D).card ≤
        ∑ z ∈ contactForceSet i.1.2 i.2,
          ((shiftedBoxFinset z D).product (shiftedBoxFinset z D)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ contactForceSet i.1.2 i.2, B * B := by
      apply Finset.sum_le_sum
      intro z hz
      calc
        ((shiftedBoxFinset z D).product
            (shiftedBoxFinset z D)).card =
            (shiftedBoxFinset z D).card *
              (shiftedBoxFinset z D).card :=
          Finset.card_product _ _
        _ ≤ B * B := by
          dsimp only [B]
          exact Nat.mul_le_mul (shiftedBoxFinset_card_le z D)
            (shiftedBoxFinset_card_le z D)
    _ = (contactForceSet i.1.2 i.2).card * (B * B) := by simp
    _ ≤ B * (B * B) := by
      gcongr
      exact contactForceSet_card_le_box hiDist
    _ = (boxFinsetBK d D).card ^ 3 := by
      simp only [B]
      ring

theorem step3TargetMultiplicity_le (T : MonotoneAutomaton d) (D N : ℕ)
    (q : FieldTriple d) :
    finiteEventMultiplicity (step3Indices (d := d) N)
      (step3TargetEvent T D N) q ≤ (boxFinsetBK d D).card ^ 3 := by
  classical
  let F := (step3Indices (d := d) N).filter fun i =>
    q ∈ step3TargetEvent T D N i
  change F.card ≤ (boxFinsetBK d D).card ^ 3
  by_cases hF : F.Nonempty
  · obtain ⟨i, hiF⟩ := hF
    have hiTarget : q ∈ step3TargetEvent T D N i :=
      (Finset.mem_filter.mp hiF).2
    have hiDist : l1dist d i.1.2 i.2 = D := hiTarget.1.2.2.1
    calc
      F.card ≤ (contactOverlapPairs i D).card := by
        apply (Finset.card_le_card_of_injOn
          (fun j : (Finset (Site d) × Site d) × Site d => (j.1.2, j.2))
          (s := F) (t := contactOverlapPairs i D))
        · intro j hjF
          have hjTarget : q ∈ step3TargetEvent T D N j :=
            (Finset.mem_filter.mp hjF).2
          obtain ⟨z, hz⟩ :=
            step3TargetEvent_forceSets_inter_nonempty T D N q hiTarget hjTarget
          have hzi : z ∈ contactForceSet i.1.2 i.2 :=
            (Finset.mem_inter.mp hz).1
          have hzj : z ∈ contactForceSet j.1.2 j.2 :=
            (Finset.mem_inter.mp hz).2
          change (j.1.2, j.2) ∈ contactOverlapPairs i D
          rw [contactOverlapPairs, Finset.mem_biUnion]
          refine ⟨z, hzi, ?_⟩
          apply Finset.mem_product.mpr
          have hzBetween := (mem_contactForceSet.mp hzj).1
          have hjDist : l1dist d j.1.2 j.2 = D := hjTarget.1.2.2.1
          constructor
          · apply mem_shiftedBoxFinset_of_l1dist_le
            rw [← l1dist_comm]
            exact (coordinateBetween_l1dist_le hzBetween).trans_eq hjDist
          · apply mem_shiftedBoxFinset_of_l1dist_le
            have hzSymm : z ∈ coordinateBetween j.2 j.1.2 := by
              intro k
              simpa [coordinateBetween, min_comm, max_comm] using hzBetween k
            rw [← l1dist_comm]
            exact (coordinateBetween_l1dist_le hzSymm).trans_eq
              ((l1dist_comm d j.2 j.1.2).trans hjDist)
        · intro j hjF k hkF heq
          have hjTarget : q ∈ step3TargetEvent T D N j :=
            (Finset.mem_filter.mp hjF).2
          have hkTarget : q ∈ step3TargetEvent T D N k :=
            (Finset.mem_filter.mp hkF).2
          have hcontacts : j.1.2 = k.1.2 ∧ j.2 = k.2 := by
            exact Prod.mk.inj heq
          have hmask : j.1.1 = k.1.1 := by
            ext z
            rw [hjTarget.1.1 z, hkTarget.1.1 z]
            simp only [pairLowInfiniteVertices_zeroHighPair]
          apply Prod.ext
          · apply Prod.ext
            · exact hmask
            · exact hcontacts.1
          · exact hcontacts.2
      _ ≤ (boxFinsetBK d D).card ^ 3 :=
        contactOverlapPairs_card_le i D hiDist
  · simp only [Finset.not_nonempty_iff_eq_empty] at hF
    rw [hF]
    simp


theorem highInsertionLowerBound_le_one
    (mu : Measure (FieldTriple d)) [IsProbabilityMeasure mu]
    (t : NNReal) (epsilon : ℝ≥0∞)
    (hinsert : HasHighInsertionLowerBound mu t epsilon) : epsilon ≤ 1 := by
  have hignore : TripleEventIgnoresHighAt (0 : Site d)
      (Set.univ : Set (FieldTriple d)) := by
    intro q q' hlow hmiddle hhigh
    simp
  have h := hinsert (0 : Site d) Set.univ MeasurableSet.univ hignore
  have htarget : mu (Set.univ ∩
      {q : FieldTriple d | t ≤ q.2.2 (0 : Site d)}) ≤ 1 := by
    calc
      mu (Set.univ ∩ {q : FieldTriple d | t ≤ q.2.2 (0 : Site d)}) ≤
          mu Set.univ := measure_mono (Set.inter_subset_left)
      _ = 1 := measure_univ
  simpa only [measure_univ, mul_one] using h.trans htarget

theorem step3SourceTarget_transfer
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu] (D N : ℕ) (epsilon : ℝ≥0∞)
    (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon)
    (i : (Finset (Site d) × Site d) × Site d) :
    epsilon ^ (boxFinsetBK d D).card * mu (step3SourceEvent T D N i) ≤
      mu (step3TargetEvent T D N i) := by
  by_cases hdist : l1dist d i.1.2 i.2 = D
  · have hcard : (contactForceSet i.1.2 i.2).card ≤
        (boxFinsetBK d D).card := contactForceSet_card_le_box hdist
    have hepsilon : epsilon ≤ 1 :=
      highInsertionLowerBound_le_one mu T.threshold epsilon hinsert
    have hpow : epsilon ^ (boxFinsetBK d D).card ≤
        epsilon ^ (contactForceSet i.1.2 i.2).card :=
      pow_le_pow_of_le_one (by positivity) hepsilon hcard
    calc
      epsilon ^ (boxFinsetBK d D).card *
          mu (step3SourceEvent T D N i) ≤
          epsilon ^ (contactForceSet i.1.2 i.2).card *
            mu (step3SourceEvent T D N i) := by gcongr
      _ ≤ mu (step3SourceEvent T D N i ∩
          highThresholdOn T.threshold (contactForceSet i.1.2 i.2)) :=
        highInsertionLowerBound_finset mu T.threshold epsilon hinsert _ _
          (measurableSet_step3SourceEvent T D N i)
          (step3SourceEvent_ignoresHigh T D N i)
      _ = mu (step3TargetEvent T D N i) := rfl
  · have hempty : step3SourceEvent T D N i = ∅ := by
      ext q
      simp [step3SourceEvent, hdist]
    rw [hempty]
    simp

theorem measurable_finiteEventMultiplicity_countable
    {Omega I : Type*} [MeasurableSpace Omega] [Countable I]
    (J : Finset I) (A : I → Set Omega)
    (hA : ∀ i ∈ J, MeasurableSet (A i)) :
    Measurable (finiteEventMultiplicity J A) := by
  classical
  let p : Omega → I → Prop := fun omega i => i ∈ J ∧ omega ∈ A i
  have hp : ∀ i, Measurable (fun omega => p omega i) := by
    intro i
    by_cases hi : i ∈ J
    · simpa [p, hi] using measurable_mem.mpr (hA i hi)
    · simp [p, hi]
  have hset : Measurable (fun omega : Omega => {i | p omega i}) :=
    measurable_setOf.comp (measurable_pi_lambda _ hp)
  have hncard : Measurable (fun omega : Omega => Set.ncard {i | p omega i}) :=
    measurable_ncard.comp hset
  convert hncard using 1
  funext omega
  unfold finiteEventMultiplicity
  let S : Set I := {i | p omega i}
  have hS : S.Finite := by
    apply J.finite_toSet.subset
    intro i hi
    exact hi.1
  rw [Set.ncard_eq_toFinset_card S hS]
  congr 1
  ext i
  simp [S, p]

theorem measurableSet_step3SourceDegree (T : MonotoneAutomaton d)
    (D N K : ℕ) : MeasurableSet {q : FieldTriple d |
      K ≤ finiteEventMultiplicity (step3Indices (d := d) N)
        (step3SourceEvent T D N) q} := by
  exact (measurable_finiteEventMultiplicity_countable
    (step3Indices (d := d) N) (step3SourceEvent T D N)
    (fun i _ => measurableSet_step3SourceEvent T D N i))
      measurableSet_Ici

theorem step3FiniteWindow_probability_bound
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu] (D N K : ℕ) (epsilon : ℝ≥0∞)
    (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon)
    (E : Set (FieldTriple d)) (hEmeas : MeasurableSet E)
    (hdegree : ∀ q ∈ E, K ≤ finiteEventMultiplicity
      (step3Indices (d := d) N) (step3SourceEvent T D N) q) :
    epsilon ^ (boxFinsetBK d D).card * K * mu E ≤
      (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞) := by
  apply finiteEventMultivalued_probability_bound mu
    (step3Indices (d := d) N) (step3SourceEvent T D N)
    (step3TargetEvent T D N)
    (fun i _ => measurableSet_step3SourceEvent T D N i)
    (fun i _ => measurableSet_step3TargetEvent T D N i)
    E hEmeas (epsilon ^ (boxFinsetBK d D).card) K
    ((boxFinsetBK d D).card ^ 3) hdegree
    (step3TargetMultiplicity_le T D N)
  intro i hi
  exact step3SourceTarget_transfer T mu D N epsilon hinsert i


end StatMech.FrontierA
