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
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling.Part3
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem independentIntersection_add_disjoint_summand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l)
    (z : IndependentFourProfiles G) :
    finiteTreeIndependentIntersectionSummand G beta J i j k l z +
      finiteTreeIndependentDisjointSummand G beta J i j k l z =
        finiteTreeIndependentTotalSummand G beta J i j k l z := by
  have hij' : grahamPairSupport i j = {i, j} := by
    unfold grahamPairSupport
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;>
      simp_all [eq_comm]
  have hkl' : grahamPairSupport k l = {k, l} := by
    unfold grahamPairSupport
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    by_cases hxk : x = k <;> by_cases hxl : x = l <;>
      simp_all [eq_comm]
  unfold finiteTreeIndependentIntersectionSummand
  unfold finiteTreeIndependentDisjointSummand
  unfold finiteTreeIndependentTotalSummand
  rw [hij', hkl']
  by_cases h1 : sources G (ofEdgeFun G z.1.1) = {i, j} <;>
    by_cases h2 : sources G (ofEdgeFun G z.1.2) = ∅ <;>
    by_cases h3 : sources G (ofEdgeFun G z.2.1) = {k, l} <;>
    by_cases h4 : sources G (ofEdgeFun G z.2.2) = ∅ <;>
    by_cases h : ∃ y : V,
      CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
      CurrentConnected G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y <;>
    simp [h1, h2, h3, h4, h] <;> ring

theorem finiteTreeIndependentTotal_eq_sourcePairProducts
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) :
    (∑' z : IndependentFourProfiles G,
      finiteTreeIndependentTotalSummand G beta J i j k l z) =
      sourcePairSum G beta J {i, j} ∅ *
        sourcePairSum G beta J {k, l} ∅ := by
  let f : IndependentPairProfiles G -> Real := fun pq =>
    (if sources G (ofEdgeFun G pq.1) = {i, j}
      then weight G beta J (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = ∅
      then weight G beta J (ofEdgeFun G pq.2) else 0)
  let g : IndependentPairProfiles G -> Real := fun pq =>
    (if sources G (ofEdgeFun G pq.1) = {k, l}
      then weight G beta J (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = ∅
      then weight G beta J (ofEdgeFun G pq.2) else 0)
  have hf : Summable f := by
    simpa only [f, if_true, mul_one] using
      (summable_gatedSourcePairSummand G beta J {i, j} ∅ (fun _ => True))
  have hg : Summable g := by
    simpa only [g, if_true, mul_one] using
      (summable_gatedSourcePairSummand G beta J {k, l} ∅ (fun _ => True))
  have hprod : Summable (fun z : IndependentFourProfiles G =>
      f z.1 * g z.2) :=
    summable_mul_of_summable_norm hf.norm hg.norm
  change (∑' z : IndependentFourProfiles G, f z.1 * g z.2) =
    (∑' pq : IndependentPairProfiles G, f pq) *
      ∑' pq : IndependentPairProfiles G, g pq
  exact (Summable.tsum_mul_tsum hf hg hprod).symm


theorem finiteTreeIndependentIntersection_add_disjoint
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeIndependentIntersectionFourMass G beta J i j k l +
      finiteTreeIndependentDisjointFourMass G beta J i j k l =
        sourcePairSum G beta J {i, j} ∅ *
          sourcePairSum G beta J {k, l} ∅ := by
  have hi := summable_finiteTreeIndependentIntersectionSummand
    G beta J i j k l
  have hd := summable_finiteTreeIndependentDisjointSummand
    G beta J hij hkl
  rw [finiteTreeIndependentIntersectionFourMass,
    finiteTreeIndependentDisjointFourMass,
    ← Summable.tsum_add hi hd]
  calc
    (∑' z : IndependentFourProfiles G,
      (finiteTreeIndependentIntersectionSummand G beta J i j k l z +
        finiteTreeIndependentDisjointSummand G beta J i j k l z)) =
      ∑' z : IndependentFourProfiles G,
        finiteTreeIndependentTotalSummand G beta J i j k l z := by
          apply tsum_congr
          exact independentIntersection_add_disjoint_summand
            G beta J hij hkl
    _ = _ := finiteTreeIndependentTotal_eq_sourcePairProducts
      G beta J i j k l


theorem finiteTreeMixedFourMass_add_disconnection
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeMixedFourMass G beta J i j k l +
        sourcePairDisconnSum G beta J {i, j} {k, l} i k *
          currentSum G beta J ∅ ^ 2 =
      sourcePairSum G beta J {i, j} ∅ *
        sourcePairSum G beta J {k, l} ∅ := by
  have hij' : grahamPairSupport i j = {i, j} := by
    unfold grahamPairSupport
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;>
      simp_all [eq_comm]
  have hkl' : grahamPairSupport k l = {k, l} := by
    unfold grahamPairSupport
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    by_cases hxk : x = k <;> by_cases hxl : x = l <;>
      simp_all [eq_comm]
  have hsplit := gatedSourcePairSum_split G beta J {i, j} {k, l}
    (fun _ => True) (fun n => CurrentConnected G n i k)
  have hpartition :
      gatedSourcePairSum G beta J {i, j} {k, l}
          (fun n => CurrentConnected G n i k) +
        sourcePairDisconnSum G beta J {i, j} {k, l} i k =
      sourcePairSum G beta J {i, j} {k, l} := by
    rw [gatedSourcePairSum_true] at hsplit
    have hconn : gatedSourcePairSum G beta J {i, j} {k, l}
        (fun n => True ∧ CurrentConnected G n i k) =
        gatedSourcePairSum G beta J {i, j} {k, l}
          (fun n => CurrentConnected G n i k) := by
      apply gatedSourcePairSum_congr_sources
      intro p q hp hq
      simp
    have hdisc : gatedSourcePairSum G beta J {i, j} {k, l}
        (fun n => True ∧ ¬ CurrentConnected G n i k) =
        sourcePairDisconnSum G beta J {i, j} {k, l} i k := by
      change gatedSourcePairSum G beta J {i, j} {k, l}
        (fun n => True ∧ ¬ CurrentConnected G n i k) =
          gatedSourcePairSum G beta J {i, j} {k, l}
            (fun n => ¬ CurrentConnected G n i k)
      apply gatedSourcePairSum_congr_sources
      intro p q hp hq
      simp
    rw [hconn, hdisc] at hsplit
    exact hsplit.symm
  rw [finiteTreeMixedFourMass_eq, hij', hkl']
  calc
    gatedSourcePairSum G beta J {i, j} {k, l}
          (fun n => CurrentConnected G n i k) *
          currentSum G beta J ∅ ^ 2 +
        sourcePairDisconnSum G beta J {i, j} {k, l} i k *
          currentSum G beta J ∅ ^ 2 =
      (gatedSourcePairSum G beta J {i, j} {k, l}
          (fun n => CurrentConnected G n i k) +
        sourcePairDisconnSum G beta J {i, j} {k, l} i k) *
          currentSum G beta J ∅ ^ 2 := by ring
    _ = sourcePairSum G beta J {i, j} {k, l} *
          currentSum G beta J ∅ ^ 2 := by rw [hpartition]
    _ = sourcePairSum G beta J {i, j} ∅ *
          sourcePairSum G beta J {k, l} ∅ := by
      rw [sourcePairSum_eq_mul, sourcePairSum_eq_mul,
        sourcePairSum_eq_mul]
      ring


theorem finiteTreeMixedFourMass_le_independentIntersection
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeMixedFourMass G beta J i j k l <=
      finiteTreeIndependentIntersectionFourMass G beta J i j k l := by
  have hdisj :=
    finiteTreeIndependentDisjointComponentMass_le_mixedDisconnection
      G beta J hbeta hJ hij hkl
  rw [finiteTreeIndependentDisjointComponentMass_eq_fourMass
    G beta J hij hkl] at hdisj
  have hmix := finiteTreeMixedFourMass_add_disconnection
    G beta J hij hkl
  have hinter := finiteTreeIndependentIntersection_add_disjoint
    G beta J hij hkl
  linarith


theorem finiteTreeMixedFourMass_le_sum_separated
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeMixedFourMass G beta J i j k l <=
      ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y :=
  (finiteTreeMixedFourMass_le_independentIntersection
    G beta J hbeta hJ hij hkl).trans
      (finiteTreeIndependentIntersectionFourMass_le_sum_separated
        G beta J hbeta hJ i j k l)


theorem finiteIsing_treeDiagram_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    0 <= -finiteIsingFourthUrsell G beta J i j k l ∧
      -finiteIsingFourthUrsell G beta J i j k l <=
        2 * finiteCurrentTreeDiagram G beta J i j k l := by
  have hfour := finiteTreeMixedFourMass_le_sum_separated
    G beta J hbeta hJ hij hkl
  have hmass :
      gatedSourcePairSum G beta J {i, j, k, l} ∅
          (fun m => grahamAllThreeConnected G m i j k l) *
            currentSum G beta J ∅ ^ 2 <=
        finiteCurrentTreeDiagramMass G beta J i j k l := by
    rw [← finiteTreeMixedFourMass_eq_allThree G beta J
      hij hik hil hjk hjl hkl]
    rw [← sum_finiteTreeSeparatedFourMass_eq_treeDiagramMass]
    exact hfour
  exact finiteIsing_treeDiagram_bound_of_mass G beta J hbeta hJ
    hij hik hil hjk hjl hkl hmass

end StatMech.FrontierA
