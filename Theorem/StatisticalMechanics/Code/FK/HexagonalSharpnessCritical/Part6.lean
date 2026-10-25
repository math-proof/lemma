/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.HexagonalTranslatedArm.Part4
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Def.StatisticalMechanics.Code.FK.HexagonalSharpnessCritical.Part6
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem hexagonalOuterInnerTheta_le_bufferedRootArmMass
    (j N : Nat) (hjn : hexagonal.bufferedRadius j < N)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    hexagonalOuterInnerTheta q beta N ≤
      hexagonalBufferedRootArmMass j (1 - Real.exp (-beta)) q := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  let incl := hexagonalBufferedToBox j N (by omega :
    hexagonal.bufferedRadius j ≤ 2 * N)
  have hdom := ocd_wired_inner_dominated_bcProb
    (Gin := hexagonal.bufferedGraph j)
    (Gout := hexagonalBoxGraph (2 * N))
    (ιV := incl)
    (bdryOut := fun y => y ∈ hexagonalBoxShell (2 * N) (2 * N))
    (hexagonalBufferedToBox_injective j N (by omega))
    (hexagonalBufferedToBox_adjMatch j N (by omega))
    (hexagonal.bufferedBoundary j) hp hp1 hq
    (hexagonalBufferedToBox_inducedWiring_le j N hjn)
    (hexagonal.bufferedRootBoundaryEvent_isIncreasing j)
  have hmono := finiteWiredEventMass_mono
    (hexagonalBoxGraph (2 * N))
    (fun y => y ∈ hexagonalBoxShell (2 * N) (2 * N))
    hp hp1 (zero_lt_one.trans_le hq)
    (hexagonalCenteredShellFullEvent_subset_bufferedRestrict j N hjn)
  rw [← hexagonalCenteredFullMass_eq_outerInnerTheta
    N (by omega) q beta hq hbeta]
  unfold hexagonalBufferedRootArmMass finiteWiredEventMass
  exact hmono.trans (by
    simpa only [bcProb_clique_eq_wiredFkProb] using hdom)

theorem hexagonalBufferedRestrictLE_self
    (j : Nat) (omega : ConfigSpace (Sym2 (hexagonal.BufferedVertex j))) :
    hexagonal.bufferedRestrictLE (le_refl j) omega = omega := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      change omega s(hexagonal.bufferedVertexInclLE (le_refl j) x,
          hexagonal.bufferedVertexInclLE (le_refl j) y) = omega s(x, y)
      have hx : hexagonal.bufferedVertexInclLE (le_refl j) x = x := by
        apply Subtype.ext
        rfl
      have hy : hexagonal.bufferedVertexInclLE (le_refl j) y = y := by
        apply Subtype.ext
        rfl
      rw [hx, hy]

theorem hexagonalBufferedRootArmMass_eq_measure
    (j : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    hexagonalBufferedRootArmMass j p q =
      (hexagonal.wiredBufferedMeasure j hp hp1 hq :
        Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder j
          (hexagonal.bufferedRootBoundaryEvent j)) := by
  rw [hexagonal.wiredBufferedMeasure_real_cylinder (le_refl j)
    hp hp1 hq (hexagonal.bufferedRootBoundaryEvent j)]
  have hpre : hexagonal.bufferedRestrictLE (le_refl j) ⁻¹'
      hexagonal.bufferedRootBoundaryEvent j =
      hexagonal.bufferedRootBoundaryEvent j := by
    ext omega
    simp only [Set.mem_preimage, hexagonalBufferedRestrictLE_self]
  rw [hpre]
  unfold hexagonalBufferedRootArmMass finiteWiredEventMass
  rfl

theorem hexagonalBufferedRootArmMass_tendsto
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun j => hexagonalBufferedRootArmMass j p q) atTop
      (nhds (hexagonal.wiredPercolationProbability p q)) := by
  have hdiag := hexagonal.wiredBufferedRootBoundary_diag_tendsto
    hp hp1 hq
  apply hdiag.congr'
  filter_upwards with j
  exact (hexagonalBufferedRootArmMass_eq_measure j hp hp1
    (zero_lt_one.trans_le hq)).symm


theorem hexagonalOuterInnerTheta_tendsto_percolation
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    Tendsto (fun n => hexagonalOuterInnerTheta q beta n) atTop
      (nhds (hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta)) q)) := by
  let p := 1 - Real.exp (-beta)
  let thetaInf := hexagonal.wiredPercolationProbability p q
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have harm : Tendsto (fun j => hexagonalBufferedRootArmMass j p q)
      atTop (nhds thetaInf) := by
    simpa [thetaInf] using hexagonalBufferedRootArmMass_tendsto hp hp1 hq
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp harm) epsilon hepsilon
  refine ⟨max 1 (hexagonal.bufferedRadius J + 1), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (Nat.le_max_left _ _).trans hn
  have hJn : hexagonal.bufferedRadius J < n := by
    have := (Nat.le_max_right 1 (hexagonal.bufferedRadius J + 1)).trans hn
    omega
  have hlower : thetaInf ≤ hexagonalOuterInnerTheta q beta n := by
    simpa [thetaInf, p] using
      hexagonal_wiredPercolationProbability_le_theta n hn1 q beta hq hbeta
  have hupper : hexagonalOuterInnerTheta q beta n ≤
      hexagonalBufferedRootArmMass J p q :=
    hexagonalOuterInnerTheta_le_bufferedRootArmMass
      J n hJn q beta hq hbeta
  have hclose := hJ J le_rfl
  rw [Real.dist_eq] at hclose ⊢
  have hclose' := (abs_lt.mp hclose).2
  rw [show p = 1 - Real.exp (-beta) by rfl] at hupper
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end StatMech.FK.PeriodicPlanar
