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
import Def.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part8
open Filter Finset Set SimpleGraph Topology
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation


@[simp] theorem mem_abbPhysicalBoundaryPairs_iff {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    {q : Option (sctBox d n) × Option (sctBox d n)} :
    q ∈ abbPhysicalBoundaryPairs d n S ↔
      q ∈ shk_boundaryPairs (withGhost (sctBoxGraph d n)) S ∧
        s(q.1, q.2) ∈ FieldGhostDict.origEdges (sctBoxGraph d n) := by
  simp [abbPhysicalBoundaryPairs]


theorem abb_origEdge_endpoints_some {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : Option V} (h : s(a, b) ∈ FieldGhostDict.origEdges G) :
    ∃ x y : V, a = some x ∧ b = some y := by
  rw [FieldGhostDict.origEdges, Finset.mem_image] at h
  obtain ⟨e, he, hmap⟩ := h
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [Sym2.map_mk, Sym2.eq_iff] at hmap
      rcases hmap with hmap | hmap
      · exact ⟨x, y, hmap.1.symm, hmap.2.symm⟩
      · exact ⟨y, x, hmap.2.symm, hmap.1.symm⟩


theorem abbPairToSite_mem_boundaryEdges {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    {q : Option (sctBox d n) × Option (sctBox d n)}
    (hq : q ∈ abbPhysicalBoundaryPairs d n S) :
    abbPairToSite d n q ∈ boundaryEdges d (abbSiteSurface d n S) := by
  obtain ⟨hqbd, hqorig⟩ := mem_abbPhysicalBoundaryPairs_iff.mp hq
  obtain ⟨hq1S, hq2S, hqadj⟩ :=
    (shk_mem_boundaryPairs (withGhost (sctBoxGraph d n)) S).mp hqbd
  obtain ⟨a, b, hqa, hqb⟩ :=
    abb_origEdge_endpoints_some (sctBoxGraph d n) hqorig
  have hqeq : q = (some a, some b) := Prod.ext hqa hqb
  subst q
  rw [abbPairToSite_some_some]
  apply shk_mem_boundaryEdges_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · exact mem_abbSiteSurface_iff.mpr ⟨a.property, hq1S⟩
  · intro hb
    obtain ⟨hbbox, hbS⟩ := mem_abbSiteSurface_iff.mp hb
    have hbeq : (⟨(b : Site d), hbbox⟩ : sctBox d n) = b :=
      Subtype.ext rfl
    exact hq2S (by simpa [hbeq] using hbS)
  · simpa [withGhost, sctBoxGraph] using hqadj


theorem abbPairToSite_injectiveOn {d n : Nat}
    {S : Finset (Option (sctBox d n))} :
    Set.InjOn (abbPairToSite d n)
      (abbPhysicalBoundaryPairs d n S : Set _) := by
  intro q hq r hr hqr
  obtain ⟨hqbd, hqorig⟩ := mem_abbPhysicalBoundaryPairs_iff.mp hq
  obtain ⟨hrbd, hrorig⟩ := mem_abbPhysicalBoundaryPairs_iff.mp hr
  obtain ⟨a, b, hqa, hqb⟩ :=
    abb_origEdge_endpoints_some (sctBoxGraph d n) hqorig
  obtain ⟨c, e, hrc, hre⟩ :=
    abb_origEdge_endpoints_some (sctBoxGraph d n) hrorig
  have hqeq : q = (some a, some b) := Prod.ext hqa hqb
  have hreq : r = (some c, some e) := Prod.ext hrc hre
  subst q
  subst r
  simp only [abbPairToSite_some_some] at hqr
  have hac : a = c := Subtype.ext (congrArg Prod.fst hqr)
  have hbe : b = e := Subtype.ext (congrArg Prod.snd hqr)
  subst c
  subst e
  rfl


theorem exists_abbPhysicalBoundaryPair {d n : Nat}
    (hn : 0 < n) {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    {e : Site d × Site d}
    (he : e ∈ boundaryEdges d (abbSiteSurface d n S)) :
    ∃ q ∈ abbPhysicalBoundaryPairs d n S, abbPairToSite d n q = e := by
  obtain ⟨huS, hvS, hadj⟩ := shk_mem_boundaryEdges_iff.mp he
  obtain ⟨hubox, huGhost⟩ := mem_abbSiteSurface_iff.mp huS
  have huinner : e.1 ∈ box d (n - 1) :=
    abbSiteSurface_subset_innerBox hocc huS
  have hvbox : e.2 ∈ box d n := by
    have hstep := adj_box_step huinner hadj
    rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')] at hstep
  let u : sctBox d n := ⟨e.1, hubox⟩
  let v : sctBox d n := ⟨e.2, hvbox⟩
  let q : Option (sctBox d n) × Option (sctBox d n) := (some u, some v)
  refine ⟨q, ?_, ?_⟩
  · apply mem_abbPhysicalBoundaryPairs_iff.mpr
    constructor
    · apply (shk_mem_boundaryPairs (withGhost (sctBoxGraph d n)) S).mpr
      refine ⟨?_, ?_, ?_⟩
      · exact huGhost
      · intro hvGhost
        apply hvS
        exact mem_abbSiteSurface_iff.mpr ⟨hvbox, hvGhost⟩
      · change (sctBoxGraph d n).Adj u v
        exact hadj
    · rw [FieldGhostDict.origEdges, Finset.mem_image]
      refine ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr ?_, ?_⟩
      · exact hadj
      · simp [q]
  · rcases e with ⟨a, b⟩
    rfl


theorem image_abbPhysicalBoundaryPairs {d n : Nat}
    (hn : 0 < n) {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) :
    (abbPhysicalBoundaryPairs d n S).image (abbPairToSite d n) =
      boundaryEdges d (abbSiteSurface d n S) := by
  ext e
  constructor
  · intro he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    exact abbPairToSite_mem_boundaryEdges hocc hq
  · intro he
    obtain ⟨q, hq, hqe⟩ := exists_abbPhysicalBoundaryPair hn hocc he
    exact Finset.mem_image.mpr ⟨q, hq, hqe⟩


theorem abbPhi_eq_phi {d n : Nat} (hn : 0 < n)
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    (ho : some (sctBoxOrigin d n) ∈ S)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    abbPhi d n beta h S =
      phi d (bondParam beta) (bondParam_le_one beta)
        (abbSiteSurface d n S) := by
  let P := abbPhysicalBoundaryPairs d n S
  let p := abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h
  have hterm : ∀ q ∈ P,
      p s(q.1, q.2) *
          probV p (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
            (some (sctBoxOrigin d n)) {q.1}) =
        (bondParam beta : Real) *
          connWithinProb d (bondParam beta) (bondParam_le_one beta)
            (abbSiteSurface d n S) (abbPairToSite d n q).1 := by
    intro q hq
    have hq' : q ∈ abbPhysicalBoundaryPairs d n S := hq
    obtain ⟨hqbd, hqorig⟩ := mem_abbPhysicalBoundaryPairs_iff.mp hq'
    obtain ⟨hq1S, hq2S, hqadj⟩ :=
      (shk_mem_boundaryPairs (withGhost (sctBoxGraph d n)) S).mp hqbd
    obtain ⟨a, b, hqa, hqb⟩ :=
      abb_origEdge_endpoints_some (sctBoxGraph d n) hqorig
    have hqeq : q = (some a, some b) := Prod.ext hqa hqb
    subst q
    have hab : (sctBoxGraph d n).Adj a b := by
      simpa [withGhost] using hqadj
    simp only [Prod.fst, Prod.snd, abbPairToSite_some_some]
    dsimp only [p]
    rw [abbParams_some_some d n beta h, if_pos hab,
      abb_bondParam_coe_eq_pBeta beta hbeta]
    rw [abb_surface_conn_prob_eq_connWithin hocc ho a hq1S
      beta h hbeta hh]
  calc
    abbPhi d n beta h S =
        ∑ q ∈ P,
          p s(q.1, q.2) *
            probV p (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
              (some (sctBoxOrigin d n)) {q.1}) := by
      unfold abbPhi abmgTargetPhi mtrPhi
      simp only [P, p, abbPhysicalBoundaryPairs, Finset.sum_filter]
    _ = ∑ q ∈ P, (bondParam beta : Real) *
          connWithinProb d (bondParam beta) (bondParam_le_one beta)
            (abbSiteSurface d n S) (abbPairToSite d n q).1 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hterm q hq
    _ = (bondParam beta : Real) *
        ∑ e ∈ boundaryEdges d (abbSiteSurface d n S),
          connWithinProb d (bondParam beta) (bondParam_le_one beta)
            (abbSiteSurface d n S) e.1 := by
      rw [← image_abbPhysicalBoundaryPairs hn hocc]
      rw [Finset.mul_sum]
      rw [Finset.sum_image (abbPairToSite_injectiveOn
        (d := d) (n := n) (S := S))]
    _ = phi d (bondParam beta) (bondParam_le_one beta)
        (abbSiteSurface d n S) := by
      rfl


theorem abbPhi_ge_one_of_gt_tildePc {d n : Nat} (hn : 0 < n)
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    (ho : some (sctBoxOrigin d n) ∈ S)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hgt : tildePc d < bondParam beta) :
    1 ≤ abbPhi d n beta h S := by
  rw [abbPhi_eq_phi hn hocc ho beta h hbeta hh]
  exact phi_ge_one_of_gt_tildePc (bondParam_le_one beta) hgt
    (abbSiteSurface d n S) (origin_mem_abbSiteSurface ho)


theorem abbPhi_differentiableAt_beta (d n : Nat)
    (S : Finset (Option (sctBox d n))) (beta h : Real) :
    DifferentiableAt Real (fun b ↦ abbPhi d n b h S) beta := by
  have hparam : ∀ e : Sym2 (Option (sctBox d n)),
      DifferentiableAt Real
        (fun b ↦ abfaParams (sctBoxGraph d n) (abbCoupling d n) b h e)
        beta := by
    intro e
    unfold abfaParams abpdBetaFieldParams paramOn
    by_cases he : e ∈ FieldGhostDict.ghostEdges (sctBox d n)
    · simp [he]
    · simp [he, pBeta]
  have hprob : ∀ q : Option (sctBox d n) × Option (sctBox d n),
      DifferentiableAt Real (fun b ↦
        probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) b h)
          (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
            (some (sctBoxOrigin d n)) {q.1})) beta := by
    intro q
    have hjoint := abfa_differentiableAt_prob_joint
      (sctBoxGraph d n) (abbCoupling d n)
      (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
        (some (sctBoxOrigin d n)) {q.1}) beta h
    have hline : DifferentiableAt Real (fun b : Real ↦ (b, h)) beta :=
      differentiableAt_id.prodMk (differentiableAt_const h)
    simpa [Function.comp_def, Function.uncurry] using
      hjoint.comp beta hline
  unfold abbPhi abmgTargetPhi mtrPhi
  apply DifferentiableAt.fun_sum
  intro q hq
  by_cases he : s(q.1, q.2) ∈ FieldGhostDict.origEdges (sctBoxGraph d n)
  · simp only [he, if_true]
    exact (hparam s(q.1, q.2)).mul (hprob q)
  · simp [he]


theorem abbPhi_ge_one_of_tildePc_le {d n : Nat} (hn : 0 < n)
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    (ho : some (sctBoxOrigin d n) ∈ S)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hge : tildePc d ≤ bondParam beta) :
    1 ≤ abbPhi d n beta h S := by
  let b : Nat → Real := fun k ↦ beta + 1 / ((k : Real) + 1)
  have hb_tendsto : Tendsto b atTop (nhds beta) := by
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)
    simpa only [b, add_zero] using tendsto_const_nhds.add hz
  have hphi_tendsto : Tendsto (fun k ↦ abbPhi d n (b k) h S)
      atTop (nhds (abbPhi d n beta h S)) :=
    (abbPhi_differentiableAt_beta d n S beta h).continuousAt.tendsto.comp
      hb_tendsto
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hphi_tendsto
  apply Filter.Eventually.of_forall
  intro k
  have hbk : beta < b k := by
    dsimp [b]
    have hk : 0 < 1 / ((k : Real) + 1) := by positivity
    linarith
  have hbk0 : 0 ≤ b k := hbeta.trans hbk.le
  have hpgtReal : (bondParam beta : Real) < (bondParam (b k) : Real) := by
    rw [abb_bondParam_coe_eq_pBeta beta hbeta,
      abb_bondParam_coe_eq_pBeta (b k) hbk0]
    exact pBeta_strictMono (J := (1 : Real)) one_pos hbk
  have hpgt : bondParam beta < bondParam (b k) := by
    exact NNReal.coe_lt_coe.mp hpgtReal
  exact abbPhi_ge_one_of_gt_tildePc hn hocc ho (b k) h hbk0 hh
    (hge.trans_lt hpgt)


theorem abbMag_meanfield_of_gt_tildePc {d n : Nat} (hn : 0 < n)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hgt : tildePc d < bondParam beta) :
    1 - abbMag d n beta h ≤
      beta * deriv (fun b ↦ abbMag d n b h) beta := by
  apply abbMag_meanfield d n beta h hbeta hh
  intro S ho hocc
  exact abbPhi_ge_one_of_gt_tildePc hn hocc ho beta h hbeta hh hgt


theorem abbMag_meanfield_of_tildePc_le {d n : Nat} (hn : 0 < n)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hge : tildePc d ≤ bondParam beta) :
    1 - abbMag d n beta h ≤
      beta * deriv (fun b ↦ abbMag d n b h) beta := by
  apply abbMag_meanfield d n beta h hbeta hh
  intro S ho hocc
  exact abbPhi_ge_one_of_tildePc_le hn hocc ho beta h hbeta hh hge

end Sharpness
end StatMech
