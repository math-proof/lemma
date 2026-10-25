/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Def.StatisticalMechanics.Code.Sharpness.BkCriterion.Part3
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace


variable {E : Type*}


variable {V : Type*}


lemma isIncreasing_connEvent (G : SimpleGraph V) (A : Set V) (u : V) (B : Set V) :
    IsIncreasing (connEvent G A u B) := by
  intro ω ω' hωω' hω
  simp only [connEvent, Set.mem_setOf_eq, ConnToSet] at hω ⊢
  obtain ⟨hu, b, hb, hbB, hconn⟩ := hω
  exact ⟨hu, b, hb, hbB, hconn.mono_config G hωω'⟩


lemma isIncreasing_edgeOpenEvent (x y : V) : IsIncreasing (edgeOpenEvent (V := V) x y) := by
  intro ω ω' hωω' hω
  simp only [edgeOpenEvent, Set.mem_setOf_eq] at hω ⊢
  have hb := hωω' s(x, y)
  rw [hω] at hb
  exact le_antisymm le_top hb


set_option linter.unusedVariables false in


theorem bk_criterion_conn {ι : Type*} [Fintype V] [DecidableEq V]
    {p : ℝ≥0} (hp : p ≤ 1) (G : SimpleGraph V)
    (A S B : Set V) (u : V)
    (s : Finset ι) (boundaryPair : ι → V × V)
    (hincl : connEvent G A u B ⊆
      ⋃ i ∈ s, disjointOccurrence (connEvent G S u {(boundaryPair i).1})
        (disjointOccurrence (edgeOpenEvent (boundaryPair i).1 (boundaryPair i).2)
          (connEvent G A (boundaryPair i).2 B))) :
    (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G A u B)
      ≤ ∑ i ∈ s,
          (bernoulliProductMeasure (E := Sym2 V) p hp).real
              (connEvent G S u {(boundaryPair i).1})
          * (bernoulliProductMeasure (E := Sym2 V) p hp).real
              (edgeOpenEvent (boundaryPair i).1 (boundaryPair i).2)
          * (bernoulliProductMeasure (E := Sym2 V) p hp).real
              (connEvent G A (boundaryPair i).2 B) := by
  refine bk_criterion hp s
    (fun i => connEvent G S u {(boundaryPair i).1})
    (fun i => edgeOpenEvent (boundaryPair i).1 (boundaryPair i).2)
    (fun i => connEvent G A (boundaryPair i).2 B)
    (fun i _ => isIncreasing_connEvent G S u _)
    (fun i _ => isIncreasing_edgeOpenEvent _ _)
    (fun i _ => isIncreasing_connEvent G A _ B)
    hincl

end Sharpness
end StatMech
