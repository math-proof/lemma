/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdgeMarginal.Part2
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.FK.DensityBounds
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessDensity
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
import Theorem.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part4
import Theorem.StatisticalMechanics.Code.FK.OneSidedContinuity
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
open Set Filter Topology
open scoped BigOperators
open StatMech.FK

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fpe2_edgeProduct_toggle_invariant {p : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p (setOpen e ω) = edgeProduct G p (setClosed e ω) := by
  unfold edgeProduct
  apply Finset.prod_congr rfl
  intro e' he'
  have hne : e' ≠ e := fun h => he (h ▸ he')
  rw [setOpen_of_ne hne, setClosed_of_ne hne]


theorem fpe2_fkWeight_toggle_invariant {p q : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p q (setOpen e ω) = fkWeight G p q (setClosed e ω) := by
  unfold fkWeight
  rw [fpe2_edgeProduct_toggle_invariant G he ω,
    numClusters_congr_openSub G (openSub_setOpen_eq_setClosed_of_notMem G he ω)]


theorem fpe2_fkProb_toggle_invariant {p q : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    fkProb G p q (setOpen e ω) = fkProb G p q (setClosed e ω) := by
  unfold fkProb
  rw [fpe2_fkWeight_toggle_invariant G he ω]


theorem fpe2_wiredFkWeight_toggle_invariant (bdry : V → Prop) [DecidablePred bdry]
    {p q : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    wiredFkWeight G bdry p q (setOpen e ω) = wiredFkWeight G bdry p q (setClosed e ω) := by
  unfold wiredFkWeight
  rw [fpe2_edgeProduct_toggle_invariant G he ω]
  congr 1
  unfold StatMech.Lattice.numClustersWired StatMech.Lattice.wiredGraph
  rw [← openSub_eq_openGraph, ← openSub_eq_openGraph,
    openSub_setOpen_eq_setClosed_of_notMem G he ω]


theorem fpe2_wiredFkProb_toggle_invariant (bdry : V → Prop) [DecidablePred bdry]
    {p q : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    wiredFkProb G bdry p q (setOpen e ω) = wiredFkProb G bdry p q (setClosed e ω) := by
  unfold wiredFkProb
  rw [fpe2_wiredFkWeight_toggle_invariant G bdry he ω]


theorem fpe2_edgeMargProb_eq_openFiber (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    edgeMargProb μ e
      = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ω e = true), μ ω := by
  unfold edgeMargProb
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω e <;> simp [h]


theorem fpe2_edgeMargProb_eq_closedFiber (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    edgeMargProb μ e
      = ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false),
          μ (setOpen e ψ) := by
  rw [fpe2_edgeMargProb_eq_openFiber]
  apply Finset.sum_nbij' (fun ω => setClosed e ω) (fun ψ => setOpen e ψ)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    simp [setClosed]
  · intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢
    simp [setOpen]
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    funext x; by_cases hx : x = e
    · subst hx; simp [hω]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]
  · intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ
    funext x; by_cases hx : x = e
    · subst hx; simp [hψ]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    congr 1
    funext x; by_cases hx : x = e
    · subst hx; simp [hω]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]


theorem fpe2_closedFiber_pairMass_eq_sum (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false),
        (μ (setOpen e ψ) + μ (setClosed e ψ)) = ∑ ω, μ ω := by
  rw [Finset.sum_add_distrib]
  rw [← fpe2_edgeMargProb_eq_closedFiber μ e]
  rw [fpe2_edgeMargProb_eq_openFiber μ e]
  have hclosed : (∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false),
        μ (setClosed e ψ))
      = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ω e = false), μ ω := by
    apply Finset.sum_congr rfl
    intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ
    congr 1
    funext x; by_cases hx : x = e
    · subst hx; simp [hψ]
    · simp [setClosed_of_ne hx]
  rw [hclosed]
  have hne : (Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ω e = false))
      = Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ¬ ω e = true) := by
    ext ω; simp
  rw [hne, Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun ω : ConfigSpace (Sym2 V) => ω e = true) μ]


theorem fpe2_edgeMargProb_half_of_toggle_invariant
    (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V)
    (hsum : ∑ ω, μ ω = 1)
    (hinv : ∀ ψ : ConfigSpace (Sym2 V), μ (setOpen e ψ) = μ (setClosed e ψ)) :
    edgeMargProb μ e = 1 / 2 := by
  have hpair := fpe2_closedFiber_pairMass_eq_sum μ e
  rw [hsum] at hpair
  have h2 : ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false),
        (μ (setOpen e ψ) + μ (setClosed e ψ))
      = 2 * edgeMargProb μ e := by
    rw [fpe2_edgeMargProb_eq_closedFiber μ e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ψ _
    rw [← hinv ψ]; ring
  rw [h2] at hpair
  linarith


open StatMech.Lattice

variable {d : ℕ}


theorem fpe2_innerEdgeLE_mk (N m : ℕ) (hNm : N ≤ m) (u v : boxVerts d N) :
    innerEdgeLE d hNm (s(u, v) : Sym2 (boxVerts d N))
      = s(boxVertInclLE d hNm u, boxVertInclLE d hNm v) := by
  unfold innerEdgeLE
  rw [Sym2.map_mk]


theorem fpe2_innerEdgeLE_notMem_edgeFinset (N m : ℕ) (hNm : N ≤ m) (e' : Sym2 (boxVerts d N))
    (he' : e' ∉ (boxGraph d N).edgeFinset) :
    innerEdgeLE d hNm e' ∉ (boxGraph d m).edgeFinset := by
  induction e' with
  | h u v =>
    rw [fpe2_innerEdgeLE_mk N m hNm u v]
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he' ⊢
    intro hadj
    apply he'
    rw [boxGraph, SimpleGraph.comap_adj] at hadj ⊢
    simpa [boxVertInclLE] using hadj


theorem fpe2_free_finite_marg_nonEdge (m : ℕ) (e : Sym2 (boxVerts d m))
    (he : e ∉ (boxGraph d m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    edgeMargProb (fkProb (boxGraph d m) p 2) e = 1 / 2 :=
  fpe2_edgeMargProb_half_of_toggle_invariant (fkProb (boxGraph d m) p 2) e
    (fkProb_sum_eq_one (boxGraph d m) hp hp1 (by norm_num))
    (fun ψ => fpe2_fkProb_toggle_invariant (boxGraph d m) he ψ)


theorem fpe2_wired_finite_marg_nonEdge (m : ℕ) (e : Sym2 (boxVerts d m))
    (he : e ∉ (boxGraph d m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e = 1 / 2 :=
  fpe2_edgeMargProb_half_of_toggle_invariant
    (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e
    (wiredFkProb_sum_eq_one (boxGraph d m) (boxBoundary d m) hp hp1 (by norm_num))
    (fun ψ => fpe2_wiredFkProb_toggle_invariant (boxGraph d m) (boxBoundary d m) he ψ)


theorem fpe2_free_density_nonEdge (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∉ (boxGraph d N).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d N e') p = 1 / 2 := by
  have hlim := dfi_free_density_eq_limit N e' hp hp1
  have hconst : (fun k => edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
      (innerEdgeLE d (Nat.le_add_right N k) e')) = fun _ => (1 / 2 : ℝ) := by
    funext k
    exact fpe2_free_finite_marg_nonEdge (N+k) _
      (fpe2_innerEdgeLE_notMem_edgeFinset N (N+k) (Nat.le_add_right N k) e' he') hp hp1
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim |>.symm


theorem fpe2_wired_density_nonEdge (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∉ (boxGraph d N).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d N e') p = 1 / 2 := by
  have hlim := dfi_wired_density_eq_limit N e' hp hp1
  have hconst : (fun k => edgeMargProb
      (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
      (innerEdgeLE d (Nat.le_add_right N k) e')) = fun _ => (1 / 2 : ℝ) := by
    funext k
    exact fpe2_wired_finite_marg_nonEdge (N+k) _
      (fpe2_innerEdgeLE_notMem_edgeFinset N (N+k) (Nat.le_add_right N k) e' he') hp hp1
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim |>.symm


theorem fpe2_halfLin_rightDeriv (t : ℝ) :
    pressureRightDeriv (fun s : ℝ => (1/2) * s) t = 1/2 := by
  unfold pressureRightDeriv
  have h1 : HasDerivWithinAt (fun s : ℝ => (1/2) * s) (1/2) (Ioi t) t := by
    simpa using ((hasDerivWithinAt_id t (Ioi t)).const_mul (1/2 : ℝ))
  rw [h1.derivWithin (uniqueDiffWithinAt_Ioi t)]


theorem fpe2_halfLin_leftDeriv (t : ℝ) :
    pressureLeftDeriv (fun s : ℝ => (1/2) * s) t = 1/2 := by
  unfold pressureLeftDeriv
  have h1 : HasDerivWithinAt (fun s : ℝ => (1/2) * s) (1/2) (Iio t) t := by
    simpa using ((hasDerivWithinAt_id t (Iio t)).const_mul (1/2 : ℝ))
  rw [h1.derivWithin (uniqueDiffWithinAt_Iio t)]


theorem fpe2_halfLin_convex : ConvexOn ℝ univ (fun s : ℝ => (1/2) * s) := by
  have : (fun s : ℝ => (1/2) * s) = fun s : ℝ => (1/2 : ℝ) • s := by funext s; rfl
  rw [this]
  exact (convexOn_id convex_univ).smul (by norm_num : (0:ℝ) ≤ 1/2)


end FK
end StatMech
