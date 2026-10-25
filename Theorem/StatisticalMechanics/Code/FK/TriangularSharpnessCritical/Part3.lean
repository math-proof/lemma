/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Def.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part3
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem triangularBoxToBufferedAt_injective (k m : Nat)
    (hkm : 2 * k ≤ triangular.bufferedRadius m) :
    Function.Injective (triangularBoxToBufferedAt k m hkm) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : triangular.BufferedVertex m => (z : Site 2)) h

theorem triangularBoxToBufferedAt_adjMatch (k m : Nat)
    (hkm : 2 * k ≤ triangular.bufferedRadius m) :
    ocd_AdjMatch (triangularBoxGraph (2 * k))
      (triangular.bufferedGraph m) (triangularBoxToBufferedAt k m hkm) := by
  intro x y
  rfl

theorem triangularBoxToBufferedAt_not_boundary
    (k m : Nat) (hkm : 2 * k < m)
    (x : TriangularBoxVertex (2 * k)) :
    ¬ triangular.bufferedBoundary m
      (triangularBoxToBufferedAt k m
        ((triangular.id_le_bufferedRadius (2 * k)).trans
          (triangular.bufferedRadius_strictMono.monotone hkm.le)) x) := by
  intro hx
  have hxEarlier : x.1 ∈
      triangular.orbitBox (triangular.bufferedRadius (2 * k)) := by
    rw [triangular_mem_orbitBox_iff_box]
    exact box_mono 2 (triangular.id_le_bufferedRadius (2 * k)) x.2
  exact (triangular.bufferedBoundary_not_mem_of_lt hkm _ hx) hxEarlier

theorem triangularBoxToBufferedAt_boundary_of_adj_outside
    (k : Nat) (hk : 1 ≤ k)
    (x : TriangularBoxVertex (2 * k))
    (z : Site 2) (hxz : triangularGraph.Adj x.1 z)
    (hz : z ∉ box 2 (2 * k)) :
    x ∈ triangularBoxShell (2 * k) (2 * k) := by
  have hxtrans : x.1 ∈ triangularTransBox (2 * k) (0 : Site 2) := by
    simpa only [triangularTransBox, StatMech.FK.fvs_transBox,
      Set.mem_setOf_eq, sub_zero] using x.2
  have hztrans : z ∉ triangularTransBox (2 * k) (0 : Site 2) := by
    simpa only [triangularTransBox, StatMech.FK.fvs_transBox,
      Set.mem_setOf_eq, sub_zero] using hz
  have hboundary := triangularTransBox_boundary_of_adj_outside
    (x := (0 : Site 2)) (R := 2 * k) (by omega)
    ⟨x.1, hxtrans⟩ z hxz hztrans
  simp [triangularBoxShell, triangularTransBoxBoundary,
    vertexBoundary] at hboundary ⊢
  exact hboundary

theorem triangularBoxToBufferedAt_inducedWiring_le
    (k m : Nat) (hk : 1 ≤ k) (hkm : 2 * k < m)
    (psi : ConfigSpace (Sym2 (triangular.BufferedVertex m))) :
    ocd_inducedWiring (triangular.bufferedGraph m)
        (triangularBoxToBufferedAt k m
          ((triangular.id_le_bufferedRadius (2 * k)).trans
            (triangular.bufferedRadius_strictMono.monotone hkm.le)))
        (triangular.bufferedBoundary m) psi ≤
      boundaryCliqueGraph
        (fun x => x ∈ triangularBoxShell (2 * k) (2 * k)) := by
  let hrad : 2 * k ≤ triangular.bufferedRadius m :=
    (triangular.id_le_bufferedRadius (2 * k)).trans
      (triangular.bufferedRadius_strictMono.monotone hkm.le)
  let incl := triangularBoxToBufferedAt k m hrad
  apply StatMech.FK.ocd_comapInducedWiring_le triangularGraph incl
    (fun _ => rfl) (triangularBoxToBufferedAt_injective k m hrad)
    (triangular.bufferedBoundary m)
    (fun x => x ∈ triangularBoxShell (2 * k) (2 * k))
  · intro x
    exact triangularBoxToBufferedAt_not_boundary k m hkm x
  · intro x z hxz hz
    exact triangularBoxToBufferedAt_boundary_of_adj_outside
      k hk x z hxz hz

theorem triangularBufferedInnerShell_finite_le_theta
    (k m : Nat) (hk : 1 ≤ k) (hkm : 2 * k < m)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (triangular.wiredBufferedMeasure m
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedInnerShellEvent k)) ≤
      triangularOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have hNm : 2 * k ≤ m := hkm.le
  let hrad : 2 * k ≤ triangular.bufferedRadius m :=
    (triangular.id_le_bufferedRadius (2 * k)).trans
      (triangular.bufferedRadius_strictMono.monotone hNm)
  let incl := triangularBoxToBufferedAt k m hrad
  have hcomp : ∀ omega : ConfigSpace (Sym2 (triangular.BufferedVertex m)),
      ocd_innerRestrict (triangularBoxToBuffered k)
          (triangular.bufferedRestrictLE hNm omega) =
        ocd_innerRestrict incl omega := by
    intro omega
    funext e
    have hv : ∀ x : TriangularBoxVertex (2 * k),
        triangular.bufferedVertexInclLE hNm (triangularBoxToBuffered k x) =
          incl x := by
      intro x
      apply Subtype.ext
      rfl
    induction e using Sym2.inductionOn with
    | _ x y =>
        change omega s(triangular.bufferedVertexInclLE hNm
            (triangularBoxToBuffered k x),
          triangular.bufferedVertexInclLE hNm
            (triangularBoxToBuffered k y)) =
          omega s(incl x, incl y)
        rw [hv x, hv y]
  have hdom := ocd_wired_inner_dominated_bcProb
    (Gin := triangularBoxGraph (2 * k))
    (Gout := triangular.bufferedGraph m)
    (ιV := incl)
    (bdryOut := triangular.bufferedBoundary m)
    (triangularBoxToBufferedAt_injective k m hrad)
    (triangularBoxToBufferedAt_adjMatch k m hrad)
    (fun x => x ∈ triangularBoxShell (2 * k) (2 * k))
    hp hp1 hq
    (triangularBoxToBufferedAt_inducedWiring_le k m hk hkm)
    (triangularCenteredShellFullEvent_increasing (2 * k) k)
  rw [triangular.wiredBufferedMeasure_real_cylinder hNm hp hp1
    (zero_lt_one.trans_le hq) (triangularBufferedInnerShellEvent k)]
  have heventEq :
      triangular.bufferedRestrictLE hNm ⁻¹'
          triangularBufferedInnerShellEvent k =
        ocd_innerRestrict incl ⁻¹'
          triangularCenteredShellFullEvent (2 * k) k := by
    ext omega
    simp only [Set.mem_preimage, triangularBufferedInnerShellEvent, hcomp]
  rw [heventEq]
  calc
    (∑ omega,
        (ocd_innerRestrict incl ⁻¹'
          triangularCenteredShellFullEvent (2 * k) k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangular.bufferedGraph m)
            (triangular.bufferedBoundary m) p q omega) ≤
      ∑ omega,
        (triangularCenteredShellFullEvent (2 * k) k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangularBoxGraph (2 * k))
            (fun x => x ∈ triangularBoxShell (2 * k) (2 * k)) p q omega := by
        simpa only [bcProb_clique_eq_wiredFkProb] using hdom
    _ = triangularOuterInnerTheta q beta k := by
      simpa [p] using triangularCenteredFullMass_eq_outerInnerTheta
        k hk q beta hq hbeta

theorem triangularBufferedInnerShell_infinite_le_theta
    (k : Nat) (hk : 1 ≤ k) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (triangular.wiredBufferedInfiniteVolume
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedInnerShellEvent k)) ≤
      triangularOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have htend := triangular.wiredBufferedMeasure_tendsto_cylinder
    (2 * k) hp hp1 hq (triangularBufferedInnerShellEvent_increasing k)
  apply le_of_tendsto htend
  filter_upwards [Filter.eventually_ge_atTop (2 * k + 1)] with m hm
  exact triangularBufferedInnerShell_finite_le_theta
    k m hk (by omega) q beta hq hbeta

theorem triangular_root_eq_zero : triangular.root = (0 : Site 2) := by
  have h := triangular.root_mem_fundamentalDomain
  simpa [triangular] using h

theorem triangular_percolationEvent_subset_innerShell
    (k : Nat) (hk : 1 ≤ k) :
    triangular.percolationEvent ⊆
      triangular.bufferedCylinder (2 * k)
        (triangularBufferedInnerShellEvent k) := by
  intro omega hperc
  have hall : ∀ n, omega ∈ triangular.bufferedCylinder n
      (triangular.bufferedRootBoundaryEvent n) := by
    have hinter : omega ∈ ⋂ n, triangular.bufferedCylinder n
        (triangular.bufferedRootBoundaryEvent n) := by
      rw [triangular.iInter_bufferedRootBoundaryCylinder]
      exact hperc
    exact Set.mem_iInter.mp hinter
  obtain ⟨v, hvBoundary, hreach⟩ := hall (2 * k)
  have hfull := triangular.bufferedReachable_full (2 * k) omega hreach
  change (triangular.openSubgraph omega).Reachable triangular.root v.1 at hfull
  rw [triangular_root_eq_zero] at hfull
  have hvOutside : v.1 ∉ box 2 k := by
    intro hvbox
    have hvEarlier : v.1 ∈
        triangular.orbitBox (triangular.bufferedRadius k) := by
      rw [triangular_mem_orbitBox_iff_box]
      exact box_mono 2 (triangular.id_le_bufferedRadius k) hvbox
    exact (triangular.bufferedBoundary_not_mem_of_lt
      (show k < 2 * k by omega) v hvBoundary) hvEarlier
  have hzero : (0 : Site 2) ∈ box 2 k := by simp
  obtain ⟨y, hyReach, w, hyw, hwOutside⟩ :=
    reachable_induce_innerBoundary (triangular.openSubgraph omega)
      (box 2 k) hzero hvOutside hfull
  have hyAdj : triangularGraph.Adj y.1 w := hyw.1
  have hyShell : y.1 ∈ vertexBoundary 2 k := by
    refine ⟨y.2, ?_⟩
    intro hySmall
    exact hwOutside (triangular_adj_mem_box_of_mem_pred hk hySmall hyAdj)
  let phi : ((triangular.openSubgraph omega).induce (box 2 k)) →g
      FK.openSub (triangularBoxGraph (2 * k))
        (ocd_innerRestrict (triangularBoxToBuffered k)
          (triangular.bufferedRestrict (2 * k) omega)) := {
    toFun := fun z => (⟨z.1,
      box_mono 2 (by omega : k ≤ 2 * k) z.2⟩ :
        TriangularBoxVertex (2 * k))
    map_rel' := by
      intro a b hab
      change triangularGraph.Adj a.1 b.1 ∧ omega s(a.1, b.1) = true at hab
      rw [FK.openSub_adj]
      refine ⟨hab.1, ?_⟩
      simpa [ocd_innerRestrict, ocd_innerEdge, triangularBoxToBuffered,
        PeriodicGraph.bufferedRestrict] using hab.2 }
  have hmapped := hyReach.map phi
  have hroot : phi ⟨(0 : Site 2), hzero⟩ = triangularBoxRoot (2 * k) := by
    apply Subtype.ext
    rfl
  have hyMem : phi y ∈ triangularBoxShell (2 * k) k := by
    simp only [triangularBoxShell, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hyShell
  change ocd_innerRestrict (triangularBoxToBuffered k)
      (triangular.bufferedRestrict (2 * k) omega) ∈
    triangularCenteredShellFullEvent (2 * k) k
  refine ⟨phi y, hyMem, ?_⟩
  rwa [hroot] at hmapped

theorem triangular_wiredPercolationProbability_le_theta
    (k : Nat) (hk : 1 ≤ k) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    triangular.wiredPercolationProbability
        (1 - Real.exp (-beta)) q ≤
      triangularOuterInnerTheta q beta k := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  let mu := triangular.wiredBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq)
  have hmono : (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
      triangular.percolationEvent ≤
      (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedInnerShellEvent k)) :=
    measureReal_mono (triangular_percolationEvent_subset_innerShell k hk)
      (measure_ne_top _ _)
  rw [show triangular.wiredPercolationProbability
      (1 - Real.exp (-beta)) q =
      (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
        triangular.percolationEvent by
    simp [PeriodicGraph.wiredPercolationProbability, hp, hp1,
      zero_lt_one.trans_le hq, mu]]
  exact hmono.trans
    (triangularBufferedInnerShell_infinite_le_theta k hk q beta hq hbeta)


end StatMech.FK.PeriodicPlanar
