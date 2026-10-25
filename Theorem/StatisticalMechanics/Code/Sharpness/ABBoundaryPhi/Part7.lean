/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryProfile.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part13
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Mathlib.Data.Finset.Preimage
import Def.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part6
open Filter Finset Set SimpleGraph Topology
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation


@[simp] theorem abbSiteSurfaceEquiv_apply (d n : Nat)
    (S : Finset (Option (sctBox d n)))
    (x : abbPhysicalSurface d n S) :
    ((abbSiteSurfaceEquiv d n S x : abbSiteSurface d n S) : Site d) =
      ((x : sctBox d n) : Site d) := rfl


theorem abbSurfaceEquiv_adj {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) (x y : S) :
    ((withGhost (sctBoxGraph d n)).induce (S : Set _)).Adj x y ↔
      ((sctBoxGraph d n).induce
        (abbPhysicalSurface d n S : Set _)).Adj
          (abbSurfaceEquiv hocc x) (abbSurfaceEquiv hocc y) := by
  have hx := abbSurfaceValue_spec hocc x
  have hy := abbSurfaceValue_spec hocc y
  simp only [SimpleGraph.induce_adj]
  rw [hx, hy]
  simp only [withGhost, Option.some.injEq]
  change (sctBoxGraph d n).Adj (abbSurfaceValue hocc x)
      (abbSurfaceValue hocc y) ↔
    (sctBoxGraph d n).Adj (abbSurfaceValue hocc x)
      (abbSurfaceValue hocc y)
  rfl


theorem abbSiteSurfaceEquiv_adj {d n : Nat}
    (S : Finset (Option (sctBox d n)))
    (x y : abbPhysicalSurface d n S) :
    ((sctBoxGraph d n).induce
      (abbPhysicalSurface d n S : Set _)).Adj x y ↔
      ((hypercubicLattice d).induce
        (abbSiteSurface d n S : Set _)).Adj
          (abbSiteSurfaceEquiv d n S x) (abbSiteSurfaceEquiv d n S y) := by
  simp [sctBoxGraph]


theorem abbParams_some_some (d n : Nat) (beta h : Real)
    (x y : sctBox d n) :
    abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h
        s(some x, some y) =
      if (sctBoxGraph d n).Adj x y then pBeta 1 beta else 0 := by
  by_cases hxy : (sctBoxGraph d n).Adj x y
  · have he : s(x, y) ∈ (sctBoxGraph d n).edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr hxy
    simp [abfaParams, abpdBetaFieldParams, paramOn,
      FieldGhostDict.ghostEdges, abfaLiftCoupling, abfaBaseCoupling,
      abbCoupling, hxy, he]
  · have he : s(x, y) ∉ (sctBoxGraph d n).edgeFinset := fun h ↦
      hxy (SimpleGraph.mem_edgeFinset.mp h)
    simp [abfaParams, abpdBetaFieldParams, paramOn,
      FieldGhostDict.ghostEdges, abfaLiftCoupling, abfaBaseCoupling,
      abbCoupling, hxy, he, pBeta]


theorem abb_surface_conn_prob_eq_site {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    (o x : S) (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h)
        (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
          (o : Option (sctBox d n)) {(x : Option (sctBox d n))}) =
      probV (fun _ : Sym2 (abbSiteSurface d n S) ↦ pBeta 1 beta)
        (connEvent ((hypercubicLattice d).induce
          (abbSiteSurface d n S : Set _)) Set.univ
          (abbSiteSurfaceEquiv d n S (abbSurfaceEquiv hocc o))
          {abbSiteSurfaceEquiv d n S (abbSurfaceEquiv hocc x)}) := by
  let H := withGhost (sctBoxGraph d n)
  let T := abbPhysicalSurface d n S
  let K := abbSiteSurface d n S
  let GS := H.induce (S : Set (Option (sctBox d n)))
  let GT := (sctBoxGraph d n).induce (T : Set (sctBox d n))
  let GK := (hypercubicLattice d).induce (K : Set (Site d))
  let p := abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h
  let qS : Sym2 S → Real := fun e ↦ p (Sym2.map Subtype.val e)
  let qT : Sym2 T → Real := fun e ↦
    qS ((abbEdgeEquiv (abbSurfaceEquiv hocc)).symm e)
  let r : Real := pBeta 1 beta
  have hJ : ∀ e ∈ (sctBoxGraph d n).edgeFinset,
      0 ≤ abbCoupling d n e := by
    intro e he
    simp [abbCoupling]
  have hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1 :=
    abfaParams_mem (sctBoxGraph d n) (abbCoupling d n) hJ beta h hbeta hh
  have hqT : ∀ e, 0 ≤ qT e ∧ qT e ≤ 1 := by
    intro e
    exact hp _
  have hr0 : 0 ≤ r := pBeta_nonneg (by simpa using hbeta)
  have hr1 : r ≤ 1 := (pBeta_lt_one 1 beta).le
  have hqT_edge (a b : T) (hab : GT.Adj a b) : qT s(a, b) = r := by
    have habBox : (sctBoxGraph d n).Adj (a : sctBox d n)
        (b : sctBox d n) := hab
    have hinv : (abbEdgeEquiv (abbSurfaceEquiv hocc)).symm s(a, b) =
        s((abbSurfaceEquiv hocc).symm a,
          (abbSurfaceEquiv hocc).symm b) := by
      apply (abbEdgeEquiv (abbSurfaceEquiv hocc)).injective
      simp [abbEdgeEquiv_mk]
    simp only [qT, qS, p, r]
    rw [hinv, Sym2.map_mk, abbSurfaceEquiv_symm_apply,
      abbSurfaceEquiv_symm_apply]
    rw [abbParams_some_some d n beta h]
    simp [habBox]
  let D : Finset (Sym2 T) := Finset.univ.filter fun e ↦ qT e = r
  have hDedge : ∀ a b, GT.Adj a b → s(a, b) ∈ D := by
    intro a b hab
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hqT_edge a b hab
  calc
    probV p (connEvent H (S : Set _) (o : Option (sctBox d n))
        {(x : Option (sctBox d n))}) =
        probV qS (connEvent GS Set.univ o {x}) := by
      exact abb_probV_connEvent_eq_induce H p (fun e ↦ (hp e).1)
        (fun e ↦ (hp e).2) S o x
    _ = probV qT
        (connEvent GT Set.univ (abbSurfaceEquiv hocc o)
          {abbSurfaceEquiv hocc x}) := by
      exact abb_probV_connEvent_relabel GS GT (abbSurfaceEquiv hocc)
        (abbSurfaceEquiv_adj hocc) qS o x
    _ = probV (fun _ : Sym2 T ↦ r)
        (connEvent GT Set.univ (abbSurfaceEquiv hocc o)
          {abbSurfaceEquiv hocc x}) := by
      apply abb_probV_eq_of_agreeOn qT (fun _ : Sym2 T ↦ r)
        (fun e ↦ (hqT e).1) (fun e ↦ (hqT e).2)
        (fun _ ↦ hr0) (fun _ ↦ hr1) _ D
        (abb_connEvent_univ_dependsOn_edges GT D hDedge
          (abbSurfaceEquiv hocc o) (abbSurfaceEquiv hocc x))
      intro e he
      exact (Finset.mem_filter.mp he).2
    _ = probV (fun _ : Sym2 K ↦ r)
        (connEvent GK Set.univ
          (abbSiteSurfaceEquiv d n S (abbSurfaceEquiv hocc o))
          {abbSiteSurfaceEquiv d n S (abbSurfaceEquiv hocc x)}) := by
      simpa only [GT, GK, T, K, r] using
        (abb_probV_connEvent_relabel GT GK (abbSiteSurfaceEquiv d n S)
          (abbSiteSurfaceEquiv_adj S) (fun _ : Sym2 T ↦ r)
          (abbSurfaceEquiv hocc o) (abbSurfaceEquiv hocc x))

set_option maxHeartbeats 800000 in


theorem abb_connWithinProb_eq_probV_induce {d : Nat}
    (p : NNReal) (hp : p ≤ 1) (T : Finset (Site d)) (x : Site d)
    (ho : origin d ∈ T) (hx : x ∈ T) :
    connWithinProb d p hp T x =
      probV (fun _ : Sym2 T ↦ (p : Real))
        (connEvent ((hypercubicLattice d).induce (T : Set _)) Set.univ
          (⟨origin d, ho⟩ : T) {(⟨x, hx⟩ : T)}) := by
  let A := connEvent (hypercubicLattice d) (T : Set (Site d))
    (origin d) {x}
  let F := abigInternalEdges T
  let AI := connEvent ((hypercubicLattice d).induce (T : Set (Site d)))
    Set.univ (⟨origin d, ho⟩ : T) {(⟨x, hx⟩ : T)}
  have hAeq : A = withinConnEvent d (T : Set (Site d)) (origin d) x :=
    shk_connEvent_singleton_eq_connWithinEvent (T : Set (Site d))
      (origin d) x
  have hdep : StatMech.DependsOn A (F : Set (Sym2 (Site d))) :=
    abig_connEvent_dependsOn (hypercubicLattice d) T (origin d) x
  have hAcyl : A = MeasureTheory.cylinder F (ih_section A F) :=
    ih_eq_cylinder_of_dependsOn F hdep
  have hmeasure :
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp =
        inhomBernoulliProductMeasure (fun _ : Sym2 (Site d) ↦ p)
          (fun _ ↦ hp) := rfl
  rw [connWithinProb_eq p hp T x (by simpa using ho) (by simpa using hx),
    ← hAeq, hmeasure, hAcyl]
  calc
    (inhomBernoulliProductMeasure (fun _ : Sym2 (Site d) ↦ p)
        (fun _ ↦ hp)).real
        (MeasureTheory.cylinder F (ih_section A F)) =
      (inhomBernoulliProductMeasure (fun _ : F ↦ p) (fun _ ↦ hp)).real
        (ih_section A F) :=
      inhom_realProb_cylinder (fun _ : Sym2 (Site d) ↦ p)
        (fun _ ↦ hp) F _
    _ = probV (fun _ : F ↦ (p : Real)) (ih_section A F) := by
      exact abb_hom_real_eq_probV p hp (ih_section A F)
    _ = probV (fun _ : Sym2 T ↦ (p : Real)) AI := by
      exact abb_probV_section_const_eq_induce (p : Real)
        (hypercubicLattice d) T ⟨origin d, ho⟩ ⟨x, hx⟩


theorem abb_bondParam_coe_eq_pBeta (beta : Real) (hbeta : 0 ≤ beta) :
    (bondParam beta : Real) = pBeta 1 beta := by
  rw [bondParam, Real.coe_toNNReal]
  · simp [pBeta]
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))


theorem abb_surface_conn_prob_eq_connWithin {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    (ho : some (sctBoxOrigin d n) ∈ S)
    (x : sctBox d n) (hx : some x ∈ S)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h)
        (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
          (some (sctBoxOrigin d n)) {some x}) =
      connWithinProb d (bondParam beta) (bondParam_le_one beta)
        (abbSiteSurface d n S) (x : Site d) := by
  let os : S := ⟨some (sctBoxOrigin d n), ho⟩
  let xs : S := ⟨some x, hx⟩
  let op : abbPhysicalSurface d n S := abbSurfaceEquiv hocc os
  let xp : abbPhysicalSurface d n S := abbSurfaceEquiv hocc xs
  let oz : abbSiteSurface d n S := abbSiteSurfaceEquiv d n S op
  let xz : abbSiteSurface d n S := abbSiteSurfaceEquiv d n S xp
  have hoSite : origin d ∈ abbSiteSurface d n S := by
    apply mem_abbSiteSurface_iff.mpr
    refine ⟨(sctBoxOrigin d n).property, ?_⟩
    simpa [StatMech.Percolation.origin, sctBoxOrigin] using ho
  have hxSite : (x : Site d) ∈ abbSiteSurface d n S := by
    apply mem_abbSiteSurface_iff.mpr
    exact ⟨x.property, hx⟩
  have hoz : oz = (⟨origin d, hoSite⟩ : abbSiteSurface d n S) := by
    apply Subtype.ext
    simp [oz, op, os, abbSurfaceEquiv_mk_some,
      StatMech.Percolation.origin, sctBoxOrigin]
    rfl
  have hxz : xz = (⟨(x : Site d), hxSite⟩ : abbSiteSurface d n S) := by
    apply Subtype.ext
    simp [xz, xp, xs, abbSurfaceEquiv_mk_some]
  have hfinite := abb_surface_conn_prob_eq_site hocc os xs beta h hbeta hh
  have hlattice := abb_connWithinProb_eq_probV_induce
    (bondParam beta) (bondParam_le_one beta) (abbSiteSurface d n S)
    (x : Site d) hoSite hxSite
  rw [abb_bondParam_coe_eq_pBeta beta hbeta] at hlattice
  calc
    probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h)
        (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
          (some (sctBoxOrigin d n)) {some x}) =
      probV (fun _ : Sym2 (abbSiteSurface d n S) ↦ pBeta 1 beta)
        (connEvent ((hypercubicLattice d).induce
          (abbSiteSurface d n S : Set _)) Set.univ oz {xz}) := hfinite
    _ = probV (fun _ : Sym2 (abbSiteSurface d n S) ↦ pBeta 1 beta)
        (connEvent ((hypercubicLattice d).induce
          (abbSiteSurface d n S : Set _)) Set.univ
          ⟨origin d, hoSite⟩ {⟨(x : Site d), hxSite⟩}) := by
      rw [hoz, hxz]
    _ = connWithinProb d (bondParam beta) (bondParam_le_one beta)
        (abbSiteSurface d n S) (x : Site d) := hlattice.symm


theorem abb_surface_avoids_boundary {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) {x : sctBox d n} (hx : some x ∈ S) :
    (x : Site d) ∉ vertexBoundary d n := by
  have hdisj := mpi_surfaceEvent_nonempty_disjoint
    (withGhost (sctBoxGraph d n)) (abbTarget d n) S hocc
  intro hxb
  exact Set.disjoint_left.mp hdisj (by simpa using hx)
    ((some_mem_abbTarget_iff d n x).mpr hxb)


theorem abbSiteSurface_subset_innerBox {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) :
    (abbSiteSurface d n S : Set (Site d)) ⊆ box d (n - 1) := by
  intro x hx
  obtain ⟨hxbox, hxS⟩ := mem_abbSiteSurface_iff.mp hx
  exact Classical.byContradiction fun hxinner =>
    abb_surface_avoids_boundary hocc hxS ⟨hxbox, hxinner⟩


theorem origin_mem_abbSiteSurface {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (ho : some (sctBoxOrigin d n) ∈ S) :
    origin d ∈ abbSiteSurface d n S := by
  apply mem_abbSiteSurface_iff.mpr
  refine ⟨(sctBoxOrigin d n).2, ?_⟩
  simpa [origin, sctBoxOrigin] using ho


theorem abb_phi_ge_one_projected {d n : Nat} {p : NNReal}
    (hp : p ≤ 1) (hgt : tildePc d < p)
    {S : Finset (Option (sctBox d n))}
    (ho : some (sctBoxOrigin d n) ∈ S) :
    1 ≤ phi d p hp (abbSiteSurface d n S) := by
  exact phi_ge_one_of_gt_tildePc hp hgt (abbSiteSurface d n S)
    (origin_mem_abbSiteSurface ho)


end Sharpness
end StatMech
