/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FiniteGraphBoundaryDifferential
import Theorem.StatisticalMechanics.Code.OSSS.DecisionTreeReindex
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
import Def.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

theorem hexagonalOuterInnerDenom_pos
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    0 < hexagonalOuterInnerDenom n q beta := by
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalOuterInnerConn n q beta x k)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hconn0 : ∀ x k, 0 ≤ hexagonalOuterInnerConn n q beta x k := by
    intro x k
    unfold hexagonalOuterInnerConn
    exact RevealmentTranslation.mean_indicator_nonneg hmu0 _
  have hM : 0 ≤ M := by
    let x : HexagonalBoxVertex n := hexagonalBoxRoot n
    have hx : x ∈ (Finset.univ : Finset (HexagonalBoxVertex n)) := Finset.mem_univ _
    have hx0 : 0 ≤ ∑ k : ↑(Finset.Icc 1 n),
        hexagonalOuterInnerConn n q beta x k :=
      Finset.sum_nonneg fun k _ => hconn0 x k
    exact hx0.trans (Finset.le_sup'
      (fun y => ∑ k : ↑(Finset.Icc 1 n),
        hexagonalOuterInnerConn n q beta y k) hx)
  have hnR : 0 < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  unfold hexagonalOuterInnerDenom
  change 0 < 2 * (1 + M) / (n : Real)
  positivity


theorem hexagonal_outer_inner_hcov
    (n : Nat) (hn : 1 ≤ n) (q beta D : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hD : 0 < D)
    (hsum : ∀ e : (hexagonalBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean
          (FK.activeBCProb (hexagonalBoxGraph (2 * n))
            (hexagonalBoxBoundaryGraph (2 * n))
            (FK.betaParams (fun _ => 1) beta) q)
          (fun omega => if ConnOpenSet (hexagonalBoxEndU n)
            (hexagonalBoxEndV n)
            (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
            (hexagonalBoxEndU n e) (hexagonalBoxShell n k)
            then (1 : Real) else 0) +
        Lindeberg.mean
          (FK.activeBCProb (hexagonalBoxGraph (2 * n))
            (hexagonalBoxBoundaryGraph (2 * n))
            (FK.betaParams (fun _ => 1) beta) q)
          (fun omega => if ConnOpenSet (hexagonalBoxEndU n)
            (hexagonalBoxEndV n)
            (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
            (hexagonalBoxEndV n e) (hexagonalBoxShell n k)
            then (1 : Real) else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
    let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (hexagonalInnerCrossInd n) *
        (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) / D ≤
      ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : ∀ e : Sym2 (HexagonalBoxVertex (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmain := hcov_reindexed_openCross_mass mu
    (FK.activeBCProb_pos _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0)
    (FK.activeBCProb_sum_eq_one _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0)
    (FK.activeBCProb_FKGLatticeCondition _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq)
    (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n))
    (hexagonalBoxEdgeLE_injective (by omega : n ≤ 2 * n))
    (hexagonalBoxEndU n) (hexagonalBoxEndV n) (hexagonalBoxRoot n)
    (Finset.univ : Finset (hexagonalBoxGraph n).edgeSet).toList
    (by simp) (hexagonalBoxShell n) (hexagonalBoxShell n)
    (by simp) (by simp) (by
      intro k hk
      simp [hexagonalBoxShell, hexagonalBoxRoot, vertexBoundary] at hk)
    (by
      intro k m hk hkm omega h
      exact hexagonalBox_reachOpen_crosses hk hkm omega h)
    n hn D hD hsum
  simpa [mu, hexagonalInnerCrossInd] using hmain


theorem hexagonal_outer_inner_hcov_geom
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (hexagonalInnerCrossInd n) *
        (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) /
          hexagonalOuterInnerDenom n q beta ≤
      ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalOuterInnerConn n q beta x k)
  let D := 2 * (1 + M) / (n : Real)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hconn0 : ∀ x k, 0 ≤ hexagonalOuterInnerConn n q beta x k := by
    intro x k
    unfold hexagonalOuterInnerConn
    exact RevealmentTranslation.mean_indicator_nonneg hmu0 _
  have hM : 0 ≤ M := by
    let x : HexagonalBoxVertex n := hexagonalBoxRoot n
    have hx : x ∈ (Finset.univ : Finset (HexagonalBoxVertex n)) := Finset.mem_univ _
    have hx0 : 0 ≤ ∑ k : ↑(Finset.Icc 1 n),
        hexagonalOuterInnerConn n q beta x k :=
      Finset.sum_nonneg fun k _ => hconn0 x k
    exact hx0.trans (Finset.le_sup'
      (fun y => ∑ k : ↑(Finset.Icc 1 n),
        hexagonalOuterInnerConn n q beta y k) hx)
  have hnR : 0 < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hD : 0 < D := by dsimp [D]; positivity
  have hsum : ∀ e : (hexagonalBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean mu (fun omega => if ConnOpenSet
          (hexagonalBoxEndU n) (hexagonalBoxEndV n)
          (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
          (hexagonalBoxEndU n e) (hexagonalBoxShell n k)
          then (1 : Real) else 0) +
        Lindeberg.mean mu (fun omega => if ConnOpenSet
          (hexagonalBoxEndU n) (hexagonalBoxEndV n)
          (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
          (hexagonalBoxEndV n e) (hexagonalBoxShell n k)
          then (1 : Real) else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
    intro e
    have hu := Finset.le_sup'
      (fun x => ∑ k : ↑(Finset.Icc 1 n),
        hexagonalOuterInnerConn n q beta x k)
      (Finset.mem_univ (hexagonalBoxEndU n e))
    have hv := Finset.le_sup'
      (fun x => ∑ k : ↑(Finset.Icc 1 n),
        hexagonalOuterInnerConn n q beta x k)
      (Finset.mem_univ (hexagonalBoxEndV n e))
    have hcard : (Fintype.card (↑(Finset.Icc 1 n)) : Real) = n := by
      rw [Fintype.card_coe, Nat.card_Icc]
      norm_num
    rw [Finset.sum_add_distrib]
    change
      (∑ k : ↑(Finset.Icc 1 n),
          hexagonalOuterInnerConn n q beta (hexagonalBoxEndU n e) k) +
        (∑ k : ↑(Finset.Icc 1 n),
          hexagonalOuterInnerConn n q beta (hexagonalBoxEndV n e) k) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D
    calc
      _ ≤ M + M := add_le_add hu hv
      _ ≤ (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
        rw [hcard]
        dsimp [D]
        rw [mul_div_cancel₀ _ hnR.ne']
        linarith
  have hmain := hexagonal_outer_inner_hcov n hn q beta D hq hbeta hD
    (by simpa [mu] using hsum)
  simpa [hexagonalOuterInnerDenom, mu, M, D] using hmain


theorem hexagonal_outer_inner_differential_logistic
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    hexagonalOuterInnerTheta q beta n *
        (1 - hexagonalOuterInnerTheta q beta n) /
          hexagonalOuterInnerDenom n q beta ≤
      hexagonalOuterInnerThetaPrime n q beta := by
  letI : Nonempty (hexagonalBoxGraph (2 * n)).edgeSet :=
    hexagonalBoxGraph_edgeSet_nonempty (2 * n) (by omega)
  let G := hexagonalBoxGraph (2 * n)
  let C := hexagonalBoxBoundaryGraph (2 * n)
  let J : Sym2 (HexagonalBoxVertex (2 * n)) → Real := fun _ => 1
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  let f := hexagonalInnerCrossInd n
  have hJ : ∀ e, 0 < J e := fun _ => by simp [J]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hcov : Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) /
        hexagonalOuterInnerDenom n q beta ≤
      ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
    simpa [G, C, J, mu, f] using
      hexagonal_outer_inner_hcov_geom n hn q beta hq hbeta
  have hpos : ∀ omega, 0 < mu omega :=
    FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    FK.activeBCProb_FKGLatticeCondition G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq
  have hf : Monotone f := hexagonalInnerCrossInd_monotone n
  have hcov0 : ∀ e : G.edgeSet,
      0 ≤ FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e) := by
    intro e
    rw [← ActiveBoundaryDifferential.cov_activeBC_eq]
    exact LindebergTree.cov_coord_nonneg hpos hmu1 hFKG hf e
  have hderiv := FK.hasDerivAt_activeBCMean_beta_sum G C hJ hbeta hq0 f
  have hderivEq :
      deriv (fun b => FK.activeBCMean G C (FK.betaParams J b) q f) beta =
        ∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(beta * J e.1)))) *
          FK.activeBCCov G C (FK.betaParams J beta) q f
            (Lindeberg.coord e) := by
    rw [hderiv.deriv]
    simp only [FK.betaParams]
  have hpref : ∀ e : G.edgeSet,
      (1 : Real) ≤ J e.1 / (1 - Real.exp (-(beta * J e.1))) := by
    intro e
    have hden : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    simp only [J, mul_one]
    rw [le_div_iff₀ hden]
    linarith [Real.exp_pos (-beta)]
  have hRusso :
      ∑ e : G.edgeSet, FK.activeBCCov G C (FK.betaParams J beta) q f
          (Lindeberg.coord e) ≤
        deriv (fun b => FK.activeBCMean G C (FK.betaParams J b) q f) beta := by
    rw [hderivEq]
    simpa using RussoPrefactor.rp_prefactor_extraction
      (fun e : G.edgeSet => J e.1 / (1 - Real.exp (-(beta * J e.1))))
      (fun e => FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e)) 1 hpref hcov0
  have hmain := hcov.trans (by
    simpa [ActiveBoundaryDifferential.cov_activeBC_eq] using hRusso)
  have hn0 : n ≠ 0 := by omega
  simpa [hexagonalOuterInnerTheta, hexagonalOuterInnerThetaPrime,
    hn0, G, C, J, mu, f] using hmain

end StatMech.FK.PeriodicPlanar
