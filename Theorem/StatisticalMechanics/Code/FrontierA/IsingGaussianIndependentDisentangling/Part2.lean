/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIndependentDisentangling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterConfinement.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIntersectionUnionBound.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedEq22Refinement
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling.Part2
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem independentClusters_disjoint_iff_safeRegion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m n : Current V) (i k : V) :
    (¬ ∃ y : V, CurrentConnected G m i y ∧ CurrentConnected G n k y) ↔
      k ∈ finiteTreeSafeRegion G n (notConnComp G m i)ᶜ := by
  rw [mem_finiteTreeSafeRegion]
  constructor
  · intro h g hg hgn
    rw [Finset.mem_compl, mem_notConnComp] at hg
    push Not at hg
    exact h ⟨g, hg, CurrentConnected.symm G hgn⟩
  · intro h
    rintro ⟨y, hiy, hky⟩
    have hy : y ∈ (notConnComp G m i)ᶜ := by
      rw [Finset.mem_compl, mem_notConnComp]
      exact not_not.mpr hiy
    exact h y hy (CurrentConnected.symm G hky)

theorem independentDisjoint_admissible
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q r s : G.edgeFinset -> Nat)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l)
    (hp : sources G (ofEdgeFun G p) = {i, j})
    (hq : sources G (ofEdgeFun G q) = ∅)
    (hr : sources G (ofEdgeFun G r) = {k, l})
    (hs : sources G (ofEdgeFun G s) = ∅)
    (hdisj : ¬ ∃ y : V,
      CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i y ∧
      CurrentConnected G (ofEdgeFun G (fun e => r e + s e)) k y) :
    notConnComp G (ofEdgeFun G (fun e => p e + q e)) i ∈
      grahamFirstAdmissibleComponentComplements i j k l k := by
  let m := ofEdgeFun G (fun e => p e + q e)
  let n := ofEdgeFun G (fun e => r e + s e)
  have hijp := currentConnected_of_sources_pair G p hij hp
  have hijm : CurrentConnected G m i j :=
    grahamCurrentConnected_add_right G p q hijp
  have hklr := currentConnected_of_sources_pair G r hkl hr
  have hkln : CurrentConnected G n k l :=
    grahamCurrentConnected_add_right G r s hklr
  rw [grahamFirstAdmissibleComponentComplements, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_notConnComp]
    exact not_not.mpr (CurrentConnected.refl G m i)
  · rw [mem_notConnComp]
    exact not_not.mpr hijm
  · rw [mem_notConnComp]
    intro hik
    exact hdisj ⟨k, hik, CurrentConnected.refl G n k⟩
  · rw [mem_notConnComp]
    intro hil
    exact hdisj ⟨l, hil, hkln⟩
  · rw [mem_notConnComp]
    intro hik
    exact hdisj ⟨k, hik, CurrentConnected.refl G n k⟩

theorem independentDisjointSummand_eq_componentSum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l)
    (z : IndependentFourProfiles G) :
    finiteTreeIndependentDisjointSummand G beta J i j k l z =
      ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k,
        finiteTreeFirstComponentSummand G beta J i j S z.1 *
          finiteTreeConfinementSummand G beta J k l S z.2 := by
  let m := ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)
  let n := ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)
  let S₀ := notConnComp G m i
  by_cases h1 : sources G (ofEdgeFun G z.1.1) = {i, j} <;>
    by_cases h2 : sources G (ofEdgeFun G z.1.2) = ∅ <;>
    by_cases h3 : sources G (ofEdgeFun G z.2.1) = {k, l} <;>
    by_cases h4 : sources G (ofEdgeFun G z.2.2) = ∅
  · by_cases hd : ¬ ∃ y : V,
        CurrentConnected G m i y ∧ CurrentConnected G n k y
    · have hS₀ : S₀ ∈
          grahamFirstAdmissibleComponentComplements i j k l k := by
        exact independentDisjoint_admissible G z.1.1 z.1.2 z.2.1 z.2.2
          hij hkl h1 h2 h3 h4 (by simpa only [m, n] using hd)
      have hsafe : k ∈ finiteTreeSafeRegion G n S₀ᶜ :=
        (independentClusters_disjoint_iff_safeRegion G m n i k).mp hd
      have hsum :
          (∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k,
            finiteTreeFirstComponentSummand G beta J i j S z.1 *
              finiteTreeConfinementSummand G beta J k l S z.2) =
            finiteTreeFirstComponentSummand G beta J i j S₀ z.1 *
              finiteTreeConfinementSummand G beta J k l S₀ z.2 := by
        apply Finset.sum_eq_single S₀
        · intro S hS hne
          simp [finiteTreeFirstComponentSummand, S₀, m, hne.symm]
        · intro hnot
          exact (hnot hS₀).elim
      rw [hsum]
      simp [finiteTreeIndependentDisjointSummand,
          finiteTreeFirstComponentSummand,
          finiteTreeConfinementSummand, h1, h2, h3, h4, hd,
          m, n, S₀, hsafe]
    · have hnotSafe : k ∉ finiteTreeSafeRegion G n S₀ᶜ := by
        intro hsafe
        exact hd ((independentClusters_disjoint_iff_safeRegion
          G m n i k).mpr hsafe)
      have hex : ∃ y : V,
          CurrentConnected G m i y ∧ CurrentConnected G n k y :=
        not_not.mp hd
      rw [finiteTreeIndependentDisjointSummand]
      simp [h1, h2, h3, h4, m, n, hex]
      symm
      apply Finset.sum_eq_zero
      intro S hS
      by_cases heq : S₀ = S
      · subst S
        simp [finiteTreeFirstComponentSummand,
          finiteTreeConfinementSummand, h1, h2, h3, h4,
          S₀, m, n, hnotSafe]
      · simp [finiteTreeFirstComponentSummand, S₀, m, heq]
  all_goals
    simp [finiteTreeIndependentDisjointSummand,
      finiteTreeFirstComponentSummand,
      finiteTreeConfinementSummand, h1, h2, h3, h4]

theorem grahamFirstComponentFiber_eq_tsum_summand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j : V) (S : Finset V) :
    grahamFirstComponentFiber G beta J S i {i, j} ∅ =
      ∑' pq : IndependentPairProfiles G,
        finiteTreeFirstComponentSummand G beta J i j S pq := by
  rfl

theorem finiteTreeClusterConfinementMass_eq_tsum_summand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (k l : V) (S : Finset V) :
    finiteTreeClusterConfinementMass G beta J k l S =
      ∑' pq : IndependentPairProfiles G,
        finiteTreeConfinementSummand G beta J k l S pq := by
  rfl


theorem finiteTreeIndependentDisjointComponentMass_eq_fourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeIndependentDisjointComponentMass G beta J i j k l =
      finiteTreeIndependentDisjointFourMass G beta J i j k l := by
  let A := grahamFirstAdmissibleComponentComplements i j k l k
  have hf (S : Finset V) : Summable
      (finiteTreeFirstComponentSummand G beta J i j S) := by
    simpa only [finiteTreeFirstComponentSummand] using
      (summable_gatedSourcePairSummand G beta J {i, j} ∅
        (fun n => notConnComp G n i = S))
  have hg (S : Finset V) : Summable
      (finiteTreeConfinementSummand G beta J k l S) := by
    simpa only [finiteTreeConfinementSummand] using
      (summable_gatedSourcePairSummand G beta J {k, l} ∅
        (fun n => k ∈ finiteTreeSafeRegion G n Sᶜ))
  have hprod (S : Finset V) : Summable (fun z : IndependentFourProfiles G =>
      finiteTreeFirstComponentSummand G beta J i j S z.1 *
        finiteTreeConfinementSummand G beta J k l S z.2) :=
    summable_mul_of_summable_norm (hf S).norm (hg S).norm
  unfold finiteTreeIndependentDisjointComponentMass
  calc
    (∑ S ∈ A,
        grahamFirstComponentFiber G beta J S i {i, j} ∅ *
          finiteTreeClusterConfinementMass G beta J k l S) =
        ∑ S ∈ A, ∑' z : IndependentFourProfiles G,
          finiteTreeFirstComponentSummand G beta J i j S z.1 *
            finiteTreeConfinementSummand G beta J k l S z.2 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [grahamFirstComponentFiber_eq_tsum_summand,
        finiteTreeClusterConfinementMass_eq_tsum_summand]
      exact Summable.tsum_mul_tsum (hf S) (hg S) (hprod S)
    _ = ∑' z : IndependentFourProfiles G, ∑ S ∈ A,
          finiteTreeFirstComponentSummand G beta J i j S z.1 *
            finiteTreeConfinementSummand G beta J k l S z.2 := by
      exact (Summable.tsum_finsetSum (s := A)
        (fun S _ => hprod S)).symm
    _ = ∑' z : IndependentFourProfiles G,
          finiteTreeIndependentDisjointSummand G beta J i j k l z := by
      apply tsum_congr
      intro z
      exact (independentDisjointSummand_eq_componentSum
        G beta J hij hkl z).symm
    _ = finiteTreeIndependentDisjointFourMass
          G beta J i j k l := rfl

theorem summable_finiteTreeIndependentDisjointSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    Summable (finiteTreeIndependentDisjointSummand
      G beta J i j k l) := by
  let A := grahamFirstAdmissibleComponentComplements i j k l k
  have hf (S : Finset V) : Summable
      (finiteTreeFirstComponentSummand G beta J i j S) := by
    simpa only [finiteTreeFirstComponentSummand] using
      (summable_gatedSourcePairSummand G beta J {i, j} ∅
        (fun n => notConnComp G n i = S))
  have hg (S : Finset V) : Summable
      (finiteTreeConfinementSummand G beta J k l S) := by
    simpa only [finiteTreeConfinementSummand] using
      (summable_gatedSourcePairSummand G beta J {k, l} ∅
        (fun n => k ∈ finiteTreeSafeRegion G n Sᶜ))
  have hprod (S : Finset V) : Summable (fun z : IndependentFourProfiles G =>
      finiteTreeFirstComponentSummand G beta J i j S z.1 *
        finiteTreeConfinementSummand G beta J k l S z.2) :=
    summable_mul_of_summable_norm (hf S).norm (hg S).norm
  have hsum : Summable (fun z : IndependentFourProfiles G =>
      ∑ S ∈ A, finiteTreeFirstComponentSummand G beta J i j S z.1 *
        finiteTreeConfinementSummand G beta J k l S z.2) := by
    have hfinite : ∀ T : Finset (Finset V), Summable
        (fun z : IndependentFourProfiles G =>
          ∑ S ∈ T, finiteTreeFirstComponentSummand G beta J i j S z.1 *
            finiteTreeConfinementSummand G beta J k l S z.2) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simpa using
          (summable_zero : Summable
            (fun _ : IndependentFourProfiles G => (0 : Real)))
      | @insert S T hST ih =>
          simpa [Finset.sum_insert hST] using (hprod S).add ih
    exact hfinite A
  apply hsum.congr
  intro z
  exact (independentDisjointSummand_eq_componentSum
    G beta J hij hkl z).symm

end StatMech.FrontierA
