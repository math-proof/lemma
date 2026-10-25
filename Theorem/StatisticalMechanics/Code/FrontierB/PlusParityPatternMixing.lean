/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PlusEvenMixing.Part2
import Def.StatisticalMechanics.Code.FrontierB.PlusParityPatternMixing
open MeasureTheory Set
open scoped BigOperators


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.ConfigSpace StatMech.FK

theorem currentEvenConfig_eq_not_currentLocalParity {E : Type*}
    (m : InfiniteCurrentConfig E) (e : E) :
    currentEvenConfig m e = !(currentLocalParity m e) := by
  unfold currentEvenConfig currentLocalParity
  by_cases hodd : Odd (m e)
  · have hneven : ¬ Even (m e) := Nat.not_even_iff_odd.mpr hodd
    simp [hodd, hneven]
  · have heven : Even (m e) := Nat.not_odd_iff_even.mp hodd
    simp [hodd, heven]

theorem currentEvenConfig_trace_iff {E : Type*} [DecidableEq E]
    (m : InfiniteCurrentConfig E) (S : Finset E) (odd : ↑S -> Bool) :
    (∀ e ∈ S, currentEvenConfig m e = currentParityTraceTarget S odd e) ↔
      currentLocalParity (restrictCurrent S m) = odd := by
  constructor
  · intro h
    funext i
    have hi := h i.1 i.2
    rw [currentEvenConfig_eq_not_currentLocalParity] at hi
    simp only [currentParityTraceTarget, dif_pos i.2] at hi
    exact Bool.not_inj hi
  · intro h e he
    have hi := congrFun h ⟨e, he⟩
    rw [currentEvenConfig_eq_not_currentLocalParity]
    simp only [currentParityTraceTarget, dif_pos he]
    exact congrArg (fun b : Bool => !b) hi

theorem currentEvenConfig_multiOpen_iff {E : Type*}
    (m : InfiniteCurrentConfig E) (T : Finset E) :
    currentEvenConfig m ∈ fmu_multiOpen T ↔
      m ∈ currentParityAvoidCylinder T := by
  simp only [fmu_multiOpen, Set.mem_setOf_eq, currentParityAvoidCylinder]
  constructor
  · intro h e he
    have hd : decide (Even (m e)) = true := h e he
    exact of_decide_eq_true hd
  · intro h e he
    exact decide_eq_true (h e he)


theorem currentParityPattern_indicator_eq_avoid_sum
    {E : Type*} [DecidableEq E]
    (S : Finset E) (odd : ↑S -> Bool) (m : InfiniteCurrentConfig E) :
    (currentParityPatternCylinder S odd).indicator (fun _ => (1 : Real)) m =
      ∑ T ∈ S.powerset, currentParityTraceCoeff S odd T *
        (currentParityAvoidCylinder T).indicator (fun _ => (1 : Real)) m := by
  have htrace := fmu_traceInd_expand S (currentParityTraceTarget S odd)
    (currentEvenConfig m)
  calc
    (currentParityPatternCylinder S odd).indicator (fun _ => (1 : Real)) m =
        fmu_traceInd S (currentParityTraceTarget S odd) (currentEvenConfig m) := by
          unfold fmu_traceInd
          by_cases hpat : m ∈ currentParityPatternCylinder S odd
          · rw [Set.indicator_of_mem hpat, if_pos]
            exact (currentEvenConfig_trace_iff m S odd).2 hpat
          · rw [Set.indicator_of_notMem hpat, if_neg]
            exact fun h => hpat ((currentEvenConfig_trace_iff m S odd).1 h)
    _ = ∑ T ∈ S.powerset, currentParityTraceCoeff S odd T *
          fmu_moInd T (currentEvenConfig m) := by
            simpa only [currentParityTraceCoeff] using htrace
    _ = ∑ T ∈ S.powerset, currentParityTraceCoeff S odd T *
          (currentParityAvoidCylinder T).indicator (fun _ => (1 : Real)) m := by
            apply Finset.sum_congr rfl
            intro T hT
            congr 1
            rw [fmu_moInd_eq_indicator]
            by_cases hopen : currentEvenConfig m ∈ fmu_multiOpen T
            · rw [Set.indicator_of_mem hopen,
                Set.indicator_of_mem ((currentEvenConfig_multiOpen_iff m T).1 hopen)]
            · rw [Set.indicator_of_notMem hopen,
                Set.indicator_of_notMem (fun h => hopen
                  ((currentEvenConfig_multiOpen_iff m T).2 h))]

theorem currentParityPattern_real_eq_avoid_sum
    {E : Type*} [Countable E] [DecidableEq E]
    (mu : Measure (InfiniteCurrentConfig E)) [IsProbabilityMeasure mu]
    (S : Finset E) (odd : ↑S -> Bool) :
    mu.real (currentParityPatternCylinder S odd) =
      ∑ T ∈ S.powerset, currentParityTraceCoeff S odd T *
        mu.real (currentParityAvoidCylinder T) := by
  have hpat : MeasurableSet (currentParityPatternCylinder S odd) :=
    measurableSet_currentCylinder S _
  rw [show mu.real (currentParityPatternCylinder S odd) =
      ∫ m, (currentParityPatternCylinder S odd).indicator
        (fun _ => (1 : Real)) m ∂mu by
    rw [MeasureTheory.integral_indicator_const (1 : Real) hpat]
    simp]
  simp_rw [currentParityPattern_indicator_eq_avoid_sum S odd]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_indicator_const (1 : Real)]
    · simp
    · rw [currentParityAvoidCylinder_eq_currentCylinder]
      exact measurableSet_currentCylinder T _
  · intro T hT
    apply Integrable.const_mul
    apply Integrable.indicator
    · exact integrable_const (1 : Real)
    · rw [currentParityAvoidCylinder_eq_currentCylinder]
      exact measurableSet_currentCylinder T _


theorem infinitePlusCurrentMeasure_parityPattern_real_eq {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (odd : ↑S -> Bool)
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityPatternCylinder S odd) =
      ∑ T ∈ S.powerset, currentParityTraceCoeff S odd T *
        ((∫ omega, Real.exp (-beta * edgeSpinSum T omega)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ T.card) := by
  rw [currentParityPattern_real_eq_avoid_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [infinitePlusCurrentMeasure_parityAvoid_real_eq hbeta T]
  intro e he
  exact hS (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he)

end StatMech.FrontierB
