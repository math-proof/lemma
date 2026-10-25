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
import Def.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part5
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem triangularOuterInnerTheta_le_bufferedRootArmMass
    (j N : Nat) (hjn : triangular.bufferedRadius j < N)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    triangularOuterInnerTheta q beta N ≤
      triangularBufferedRootArmMass j (1 - Real.exp (-beta)) q := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  let incl := triangularBufferedToBox j N (by omega :
    triangular.bufferedRadius j ≤ 2 * N)
  have hdom := ocd_wired_inner_dominated_bcProb
    (Gin := triangular.bufferedGraph j)
    (Gout := triangularBoxGraph (2 * N))
    (ιV := incl)
    (bdryOut := fun y => y ∈ triangularBoxShell (2 * N) (2 * N))
    (triangularBufferedToBox_injective j N (by omega))
    (triangularBufferedToBox_adjMatch j N (by omega))
    (triangular.bufferedBoundary j) hp hp1 hq
    (triangularBufferedToBox_inducedWiring_le j N hjn)
    (triangular.bufferedRootBoundaryEvent_isIncreasing j)
  have hmono := finiteWiredEventMass_mono
    (triangularBoxGraph (2 * N))
    (fun y => y ∈ triangularBoxShell (2 * N) (2 * N))
    hp hp1 (zero_lt_one.trans_le hq)
    (triangularCenteredShellFullEvent_subset_bufferedRestrict j N hjn)
  rw [← triangularCenteredFullMass_eq_outerInnerTheta
    N (by omega) q beta hq hbeta]
  unfold triangularBufferedRootArmMass finiteWiredEventMass
  exact hmono.trans (by
    simpa only [bcProb_clique_eq_wiredFkProb] using hdom)

theorem triangularBufferedRestrictLE_self
    (j : Nat) (omega : ConfigSpace (Sym2 (triangular.BufferedVertex j))) :
    triangular.bufferedRestrictLE (le_refl j) omega = omega := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      change omega s(triangular.bufferedVertexInclLE (le_refl j) x,
          triangular.bufferedVertexInclLE (le_refl j) y) = omega s(x, y)
      have hx : triangular.bufferedVertexInclLE (le_refl j) x = x := by
        apply Subtype.ext
        rfl
      have hy : triangular.bufferedVertexInclLE (le_refl j) y = y := by
        apply Subtype.ext
        rfl
      rw [hx, hy]

theorem triangularBufferedRootArmMass_eq_measure
    (j : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    triangularBufferedRootArmMass j p q =
      (triangular.wiredBufferedMeasure j hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder j
          (triangular.bufferedRootBoundaryEvent j)) := by
  rw [triangular.wiredBufferedMeasure_real_cylinder (le_refl j)
    hp hp1 hq (triangular.bufferedRootBoundaryEvent j)]
  have hpre : triangular.bufferedRestrictLE (le_refl j) ⁻¹'
      triangular.bufferedRootBoundaryEvent j =
      triangular.bufferedRootBoundaryEvent j := by
    ext omega
    simp only [Set.mem_preimage, triangularBufferedRestrictLE_self]
  rw [hpre]
  unfold triangularBufferedRootArmMass finiteWiredEventMass
  rfl

theorem triangularBufferedRootArmMass_tendsto
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun j => triangularBufferedRootArmMass j p q) atTop
      (nhds (triangular.wiredPercolationProbability p q)) := by
  have hdiag := triangular.wiredBufferedRootBoundary_diag_tendsto
    hp hp1 hq
  apply hdiag.congr'
  filter_upwards with j
  exact (triangularBufferedRootArmMass_eq_measure j hp hp1
    (zero_lt_one.trans_le hq)).symm


theorem triangularOuterInnerTheta_tendsto_percolation
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    Tendsto (fun n => triangularOuterInnerTheta q beta n) atTop
      (nhds (triangular.wiredPercolationProbability
        (1 - Real.exp (-beta)) q)) := by
  let p := 1 - Real.exp (-beta)
  let thetaInf := triangular.wiredPercolationProbability p q
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have harm : Tendsto (fun j => triangularBufferedRootArmMass j p q)
      atTop (nhds thetaInf) := by
    simpa [thetaInf] using triangularBufferedRootArmMass_tendsto hp hp1 hq
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp harm) epsilon hepsilon
  refine ⟨max 1 (triangular.bufferedRadius J + 1), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (Nat.le_max_left _ _).trans hn
  have hJn : triangular.bufferedRadius J < n := by
    have := (Nat.le_max_right 1 (triangular.bufferedRadius J + 1)).trans hn
    omega
  have hlower : thetaInf ≤ triangularOuterInnerTheta q beta n := by
    simpa [thetaInf, p] using
      triangular_wiredPercolationProbability_le_theta n hn1 q beta hq hbeta
  have hupper : triangularOuterInnerTheta q beta n ≤
      triangularBufferedRootArmMass J p q :=
    triangularOuterInnerTheta_le_bufferedRootArmMass
      J n hJn q beta hq hbeta
  have hclose := hJ J le_rfl
  rw [Real.dist_eq] at hclose ⊢
  have hclose' := (abs_lt.mp hclose).2
  rw [show p = 1 - Real.exp (-beta) by rfl] at hupper
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end StatMech.FK.PeriodicPlanar
