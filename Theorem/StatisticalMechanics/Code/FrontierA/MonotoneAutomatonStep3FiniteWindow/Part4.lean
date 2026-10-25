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
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part3
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


@[simp] theorem pairSiteLeft_zeroHighPair (T : MonotoneAutomaton d)
    (S : Finset (Site d)) (q : FieldTriple d) :
    pairSiteLeft (zeroHighPair T S q) = interpolatedSite T q := rfl

@[simp] theorem pairSiteRight_zeroHighPair (T : MonotoneAutomaton d)
    (S : Finset (Site d)) (q : FieldTriple d) :
    pairSiteRight (zeroHighPair T S q) = T (zeroFields q.2.2 S) := rfl

theorem measurable_zeroFields (S : Finset (Site d)) :
    Measurable (fun xi : NonnegativeField d => zeroFields xi S) := by
  rw [measurable_pi_iff]
  intro x
  by_cases hx : x ∈ S
  · simp [zeroFields, hx]
  · simpa [zeroFields, hx] using
      (measurable_pi_apply x : Measurable (fun xi : NonnegativeField d => xi x))

theorem measurable_zeroHighPair (T : MonotoneAutomaton d)
    (S : Finset (Site d)) :
    Measurable (zeroHighPair T S : FieldTriple d → PairSiteConfig d) := by
  unfold zeroHighPair
  exact measurable_pairSiteConfig.comp
    ((measurable_interpolatedSite T).prodMk
      (T.measurable_toFun.comp
        ((measurable_zeroFields S).comp measurable_snd.snd)))


theorem measurableSet_pairHighCluster_eq_preimage
    (f g : FieldTriple d → PairSiteConfig d) (hf : Measurable f)
    (hg : Measurable g) (root : Site d) :
    MeasurableSet {q | pairHighCluster (f q) root =
      pairHighCluster (g q) root} := by
  have heq : {q : FieldTriple d | pairHighCluster (f q) root =
      pairHighCluster (g q) root} =
      ⋂ z : Site d,
        ((f ⁻¹' {omega | z ∈ pairHighCluster omega root}) ∩
          (g ⁻¹' {omega | z ∈ pairHighCluster omega root})) ∪
        ((f ⁻¹' {omega | z ∈ pairHighCluster omega root})ᶜ ∩
          (g ⁻¹' {omega | z ∈ pairHighCluster omega root})ᶜ) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro h z
      rw [h]
      by_cases hz : z ∈ pairHighCluster (g q) root
      · exact Or.inl ⟨hz, hz⟩
      · exact Or.inr ⟨hz, hz⟩
    · intro h
      ext z
      rcases h z with hz | hz
      · exact iff_of_true hz.1 hz.2
      · exact iff_of_false hz.1 hz.2
  rw [heq]
  apply MeasurableSet.iInter
  intro z
  have hfz := hf (measurableSet_pairHighConnected root z)
  have hgz := hg (measurableSet_pairHighConnected root z)
  exact (hfz.inter hgz).union (hfz.compl.inter hgz.compl)


end StatMech.FrontierA
