/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInsertion
open MeasureTheory
open scoped ENNReal NNReal


namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


theorem tripleEventIgnoresMiddleAt_preimage_interpolatedSite
    (T : MonotoneAutomaton d) (x : Site d)
    (B : Set (ConfigSpace (Site d))) (hB : SiteEventIgnores x B) :
    TripleEventIgnoresMiddleAt x ((interpolatedSite T) ⁻¹' B) := by
  intro q q' hlow hmiddle
  apply hB
  intro y hy
  simp only [interpolatedSite_apply]
  rw [hlow, hmiddle y hy]


theorem measurableSet_middleThreshold (t : NNReal) (x : Site d) :
    MeasurableSet {q : FieldTriple d | t ≤ q.2.1 x} := by
  have hcoord : Measurable (fun q : FieldTriple d => q.2.1 x) :=
    (measurable_pi_apply x).comp measurable_snd.fst
  exact hcoord measurableSet_Ici


theorem interpolatedSite_eq_true_of_middleThreshold
    (T : MonotoneAutomaton d) (q : FieldTriple d) (x : Site d)
    (h : T.threshold ≤ q.2.1 x) : interpolatedSite T q x = true := by
  simp [interpolatedSite, h]


theorem interpolatedSiteLaw_hasInsertionLowerBound
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    (epsilon : ENNReal)
    (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon) :
    HasSiteInsertionLowerBound (interpolatedSiteLaw T mu) epsilon := by
  intro x B hBmeas hBoff
  let A : Set (FieldTriple d) := (interpolatedSite T) ⁻¹' B
  have hAmeas : MeasurableSet A := measurable_interpolatedSite T hBmeas
  have hAoff : TripleEventIgnoresMiddleAt x A :=
    tripleEventIgnoresMiddleAt_preimage_interpolatedSite T x B hBoff
  have hR3 := hinsert x A hAmeas hAoff
  have hsub : A ∩ {q : FieldTriple d | T.threshold ≤ q.2.1 x} ⊆
      (interpolatedSite T) ⁻¹' (B ∩ {eta | eta x = true}) := by
    rintro q ⟨hqA, hqt⟩
    exact ⟨hqA, interpolatedSite_eq_true_of_middleThreshold T q x hqt⟩
  have htargetMeas : MeasurableSet (B ∩ {eta | eta x = true}) := by
    apply hBmeas.inter
    exact measurableSet_eq_fun (measurable_pi_apply x) measurable_const
  calc
    epsilon * interpolatedSiteLaw T mu B = epsilon * mu A := by
      rw [interpolatedSiteLaw,
        Measure.map_apply (measurable_interpolatedSite T) hBmeas]
    _ ≤ mu (A ∩ {q : FieldTriple d | T.threshold ≤ q.2.1 x}) := hR3
    _ ≤ mu ((interpolatedSite T) ⁻¹' (B ∩ {eta | eta x = true})) :=
      measure_mono hsub
    _ = interpolatedSiteLaw T mu (B ∩ {eta | eta x = true}) := by
      rw [interpolatedSiteLaw,
        Measure.map_apply (measurable_interpolatedSite T) htargetMeas]


theorem siteInsertion_positive
    (nu : Measure (ConfigSpace (Site d))) (epsilon : ENNReal)
    (hepsilon : 0 < epsilon) (hinsert : HasSiteInsertionLowerBound nu epsilon)
    (x : Site d) (B : Set (ConfigSpace (Site d))) (hBmeas : MeasurableSet B)
    (hBoff : SiteEventIgnores x B) (hBpos : 0 < nu B) :
    0 < nu (B ∩ {eta | eta x = true}) := by
  have hle := hinsert x B hBmeas hBoff
  exact lt_of_lt_of_le (ENNReal.mul_pos hepsilon.ne' hBpos.ne') hle


end StatMech.FrontierA
