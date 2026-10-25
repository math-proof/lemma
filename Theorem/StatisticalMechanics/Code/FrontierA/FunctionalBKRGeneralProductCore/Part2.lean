/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part6
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Instance.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part2
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


theorem ae_isCoboundedUnder_ge_real {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ) :
    Filter.IsCoboundedUnder (fun a b : ℝ => a ≥ b) (ae ν) f := by
  have hexists : ∃ n : ℕ, ν {x | f x ≤ (n : ℝ)} ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : ν (⋃ n : ℕ, {x | f x ≤ (n : ℝ)}) = 0 :=
      measure_iUnion_null h
    have hunion : (⋃ n : ℕ, {x | f x ≤ (n : ℝ)}) = Set.univ := by
      ext x
      simp only [mem_iUnion, mem_setOf_eq, mem_univ, iff_true]
      exact exists_nat_ge (f x)
    rw [hunion, measure_univ] at hzero
    exact one_ne_zero hzero
  obtain ⟨n, hn⟩ := hexists
  exact Filter.IsCoboundedUnder.of_frequently_le (a := (n : ℝ))
    (frequently_ae_iff.mpr hn)


end StatMech.FrontierA
