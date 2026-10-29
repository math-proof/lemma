/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonCoarseTrifurcationGeneral.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSingleSiteStability.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MultivaluedMap
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3Bridge.Part2
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


theorem measurableSet_highThresholdOn (t : NNReal) (S : Finset (Site d)) :
    MeasurableSet (highThresholdOn (d := d) t S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [highThresholdOn]
  | @insert x S hx ih =>
      have heq : highThresholdOn (d := d) t (insert x S) =
          highThresholdOn t S ∩ {q | t ≤ q.2.2 x} := by
        ext q
        simp [highThresholdOn, and_comm]
      rw [heq]
      apply ih.inter
      have hcoord : Measurable (fun q : FieldTriple d => q.2.2 x) :=
        (measurable_pi_apply x).comp measurable_snd.snd
      exact hcoord measurableSet_Ici


theorem highOutput_eq_true_of_highThresholdOn
    (T : MonotoneAutomaton d) (q : FieldTriple d) (S : Finset (Site d))
    (hq : q ∈ highThresholdOn T.threshold S) (x : Site d) (hx : x ∈ S) :
    T q.2.2 x = true := by
  exact T.occupationThreshold q.2.2 x (hq x hx)


theorem highInsertionLowerBound_finset
    (mu : Measure (FieldTriple d)) (t : NNReal) (epsilon : ENNReal)
    (hinsert : HasHighInsertionLowerBound mu t epsilon)
    (S : Finset (Site d)) (A : Set (FieldTriple d))
    (hAmeas : MeasurableSet A) (hignore : TripleEventIgnoresHighOn S A) :
    epsilon ^ S.card * mu A ≤ mu (A ∩ highThresholdOn t S) := by
  classical
  induction S using Finset.induction_on generalizing A with
  | empty =>
      simp [highThresholdOn]
  | @insert x S hx ih =>
      let B : Set (FieldTriple d) := A ∩ {q | t ≤ q.2.2 x}
      have hxIgnore : TripleEventIgnoresHighAt x A := by
        intro q q' hlow hmiddle hhigh
        apply hignore q q' hlow hmiddle
        intro y hy
        exact hhigh y (fun hyx => hy (hyx ▸ Finset.mem_insert_self x S))
      have hsingle : epsilon * mu A ≤ mu B :=
        hinsert x A hAmeas hxIgnore
      have hBmeas : MeasurableSet B := by
        apply hAmeas.inter
        have hcoord : Measurable (fun q : FieldTriple d => q.2.2 x) :=
          (measurable_pi_apply x).comp measurable_snd.snd
        exact hcoord measurableSet_Ici
      have hBignore : TripleEventIgnoresHighOn S B := by
        intro q q' hlow hmiddle hhigh
        have hAiff : q ∈ A ↔ q' ∈ A := by
          apply hignore q q' hlow hmiddle
          intro y hyInsert
          exact hhigh y (fun hyS => hyInsert (Finset.mem_insert_of_mem hyS))
        have hxEq : q.2.2 x = q'.2.2 x := hhigh x hx
        simp only [B, Set.mem_inter_iff, Set.mem_setOf_eq]
        rw [hAiff, hxEq]
      have hrec := ih B hBmeas hBignore
      have hsets : B ∩ highThresholdOn t S =
          A ∩ highThresholdOn t (insert x S) := by
        ext q
        simp [B, highThresholdOn, and_left_comm, and_assoc]
      rw [hsets] at hrec
      rw [Finset.card_insert_of_notMem hx, pow_succ]
      calc
        epsilon ^ S.card * epsilon * mu A =
            epsilon ^ S.card * (epsilon * mu A) := by ring
        _ ≤ epsilon ^ S.card * mu B := by gcongr
        _ ≤ mu (A ∩ highThresholdOn t (insert x S)) := hrec


end StatMech.FrontierA
