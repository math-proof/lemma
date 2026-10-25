/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw.Part4
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part2
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


@[simp] theorem interpolatedSite_apply (T : MonotoneAutomaton d)
    (q : FieldTriple d) (x : Site d) :
    interpolatedSite T q x =
      (T q.1 x || decide (T.threshold ≤ q.2.1 x)) :=
  rfl


theorem measurable_interpolatedSite (T : MonotoneAutomaton d) :
    Measurable (interpolatedSite T : FieldTriple d → ConfigSpace (Site d)) := by
  rw [measurable_pi_iff]
  intro x
  change Measurable (fun q : FieldTriple d =>
    T q.1 x || decide (T.threshold ≤ q.2.1 x))
  have hT : Measurable (fun q : FieldTriple d => T q.1 x) :=
    measurable_pi_iff.mp (T.measurable_toFun.comp measurable_fst) x
  have hcoord : Measurable (fun q : FieldTriple d => q.2.1 x) :=
    (measurable_pi_apply x).comp measurable_snd.fst
  have hthreshold : Measurable (fun q : FieldTriple d =>
      decide (T.threshold ≤ q.2.1 x)) := by
    apply measurable_to_bool
    convert hcoord (measurableSet_Ici : MeasurableSet (Set.Ici T.threshold)) using 1
    ext q
    simp
  have hor : Measurable (fun p : Bool × Bool => p.1 || p.2) :=
    Measurable.of_discrete
  exact hor.comp (hT.prodMk hthreshold)


theorem interpolatedSite_shift (T : MonotoneAutomaton d)
    (g : Multiplicative (Site d)) (q : FieldTriple d) :
    interpolatedSite T (tripleFieldShift g q) =
      shift g (interpolatedSite T q) := by
  funext x
  simp only [interpolatedSite, tripleFieldShift_fst,
    tripleFieldShift_snd_fst, T.equivariant, shift_apply, fieldShift_apply]
  rfl


theorem automatonLow_le_interpolated (T : MonotoneAutomaton d)
    (q : FieldTriple d) : T q.1 ≤ interpolatedSite T q := by
  intro x
  cases h : T q.1 x <;> simp [interpolatedSite, h]


theorem interpolated_le_automatonMiddle (T : MonotoneAutomaton d)
    (q : FieldTriple d) (hq : IsMonotoneFieldTriple q) :
    interpolatedSite T q ≤ T q.2.1 := by
  have hmono : T q.1 ≤ T q.2.1 := T.monotone hq.1
  intro x
  by_cases ht : T.threshold ≤ q.2.1 x
  · have hopen : T q.2.1 x = true := T.occupationThreshold q.2.1 x ht
    simp [hopen]
  · simpa [interpolatedSite, ht] using hmono x


theorem automatonMiddle_le_automatonHigh (T : MonotoneAutomaton d)
    (q : FieldTriple d) (hq : IsMonotoneFieldTriple q) :
    T q.2.1 ≤ T q.2.2 :=
  T.monotone hq.2


theorem monotoneAutomaton_interpolation_sandwich (T : MonotoneAutomaton d)
    (q : FieldTriple d) (hq : IsMonotoneFieldTriple q) :
    T q.1 ≤ interpolatedSite T q ∧
      interpolatedSite T q ≤ T q.2.1 ∧ T q.2.1 ≤ T q.2.2 :=
  ⟨automatonLow_le_interpolated T q,
    interpolated_le_automatonMiddle T q hq,
    automatonMiddle_le_automatonHigh T q hq⟩


end StatMech.FrontierA
