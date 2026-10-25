/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FiniteGraphBoundaryDifferential
import Theorem.StatisticalMechanics.Code.OSSS.DecisionTreeReindex
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
import Def.StatisticalMechanics.Code.FK.TriangularSharpness.Part5
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

theorem triangularOuterInnerDenom_pos
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    0 < triangularOuterInnerDenom n q beta := by
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (TriangularBoxVertex n)).sup'
    ⟨triangularBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ k : ↑(Finset.Icc 1 n),
      triangularOuterInnerConn n q beta x k)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hconn0 : ∀ x k, 0 ≤ triangularOuterInnerConn n q beta x k := by
    intro x k
    unfold triangularOuterInnerConn
    exact RevealmentTranslation.mean_indicator_nonneg hmu0 _
  have hM : 0 ≤ M := by
    let x : TriangularBoxVertex n := triangularBoxRoot n
    have hx : x ∈ (Finset.univ : Finset (TriangularBoxVertex n)) := Finset.mem_univ _
    have hx0 : 0 ≤ ∑ k : ↑(Finset.Icc 1 n),
        triangularOuterInnerConn n q beta x k :=
      Finset.sum_nonneg fun k _ => hconn0 x k
    exact hx0.trans (Finset.le_sup'
      (fun y => ∑ k : ↑(Finset.Icc 1 n),
        triangularOuterInnerConn n q beta y k) hx)
  have hnR : 0 < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  unfold triangularOuterInnerDenom
  change 0 < 2 * (1 + M) / (n : Real)
  positivity


theorem triangular_outer_inner_hcov
    (n : Nat) (hn : 1 ≤ n) (q beta D : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hD : 0 < D)
    (hsum : ∀ e : (triangularBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean
          (FK.activeBCProb (triangularBoxGraph (2 * n))
            (triangularBoxBoundaryGraph (2 * n))
            (FK.betaParams (fun _ => 1) beta) q)
          (fun omega => if ConnOpenSet (triangularBoxEndU n)
            (triangularBoxEndV n)
            (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
            (triangularBoxEndU n e) (triangularBoxShell n k)
            then (1 : Real) else 0) +
        Lindeberg.mean
          (FK.activeBCProb (triangularBoxGraph (2 * n))
            (triangularBoxBoundaryGraph (2 * n))
            (FK.betaParams (fun _ => 1) beta) q)
          (fun omega => if ConnOpenSet (triangularBoxEndU n)
            (triangularBoxEndV n)
            (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
            (triangularBoxEndV n e) (triangularBoxShell n k)
            then (1 : Real) else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
    let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
      (triangularBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (triangularInnerCrossInd n) *
        (1 - Lindeberg.mean mu (triangularInnerCrossInd n)) / D ≤
      ∑ e, Lindeberg.cov mu (triangularInnerCrossInd n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : ∀ e : Sym2 (TriangularBoxVertex (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmain := hcov_reindexed_openCross_mass mu
    (FK.activeBCProb_pos _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0)
    (FK.activeBCProb_sum_eq_one _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0)
    (FK.activeBCProb_FKGLatticeCondition _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq)
    (triangularBoxEdgeLE (by omega : n ≤ 2 * n))
    (triangularBoxEdgeLE_injective (by omega : n ≤ 2 * n))
    (triangularBoxEndU n) (triangularBoxEndV n) (triangularBoxRoot n)
    (Finset.univ : Finset (triangularBoxGraph n).edgeSet).toList
    (by simp) (triangularBoxShell n) (triangularBoxShell n)
    (by simp) (by simp) (by
      intro k hk
      simp [triangularBoxShell, triangularBoxRoot, vertexBoundary] at hk)
    (by
      intro k m hk hkm omega h
      exact triangularBox_reachOpen_crosses hk hkm omega h)
    n hn D hD hsum
  simpa [mu, triangularInnerCrossInd] using hmain


theorem triangular_outer_inner_hcov_geom
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
      (triangularBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (triangularInnerCrossInd n) *
        (1 - Lindeberg.mean mu (triangularInnerCrossInd n)) /
          triangularOuterInnerDenom n q beta ≤
      ∑ e, Lindeberg.cov mu (triangularInnerCrossInd n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (TriangularBoxVertex n)).sup'
    ⟨triangularBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ k : ↑(Finset.Icc 1 n),
      triangularOuterInnerConn n q beta x k)
  let D := 2 * (1 + M) / (n : Real)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hconn0 : ∀ x k, 0 ≤ triangularOuterInnerConn n q beta x k := by
    intro x k
    unfold triangularOuterInnerConn
    exact RevealmentTranslation.mean_indicator_nonneg hmu0 _
  have hM : 0 ≤ M := by
    let x : TriangularBoxVertex n := triangularBoxRoot n
    have hx : x ∈ (Finset.univ : Finset (TriangularBoxVertex n)) := Finset.mem_univ _
    have hx0 : 0 ≤ ∑ k : ↑(Finset.Icc 1 n),
        triangularOuterInnerConn n q beta x k :=
      Finset.sum_nonneg fun k _ => hconn0 x k
    exact hx0.trans (Finset.le_sup'
      (fun y => ∑ k : ↑(Finset.Icc 1 n),
        triangularOuterInnerConn n q beta y k) hx)
  have hnR : 0 < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hD : 0 < D := by dsimp [D]; positivity
  have hsum : ∀ e : (triangularBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean mu (fun omega => if ConnOpenSet
          (triangularBoxEndU n) (triangularBoxEndV n)
          (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
          (triangularBoxEndU n e) (triangularBoxShell n k)
          then (1 : Real) else 0) +
        Lindeberg.mean mu (fun omega => if ConnOpenSet
          (triangularBoxEndU n) (triangularBoxEndV n)
          (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
          (triangularBoxEndV n e) (triangularBoxShell n k)
          then (1 : Real) else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
    intro e
    have hu := Finset.le_sup'
      (fun x => ∑ k : ↑(Finset.Icc 1 n),
        triangularOuterInnerConn n q beta x k)
      (Finset.mem_univ (triangularBoxEndU n e))
    have hv := Finset.le_sup'
      (fun x => ∑ k : ↑(Finset.Icc 1 n),
        triangularOuterInnerConn n q beta x k)
      (Finset.mem_univ (triangularBoxEndV n e))
    have hcard : (Fintype.card (↑(Finset.Icc 1 n)) : Real) = n := by
      rw [Fintype.card_coe, Nat.card_Icc]
      norm_num
    rw [Finset.sum_add_distrib]
    change
      (∑ k : ↑(Finset.Icc 1 n),
          triangularOuterInnerConn n q beta (triangularBoxEndU n e) k) +
        (∑ k : ↑(Finset.Icc 1 n),
          triangularOuterInnerConn n q beta (triangularBoxEndV n e) k) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D
    calc
      _ ≤ M + M := add_le_add hu hv
      _ ≤ (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
        rw [hcard]
        dsimp [D]
        rw [mul_div_cancel₀ _ hnR.ne']
        linarith
  have hmain := triangular_outer_inner_hcov n hn q beta D hq hbeta hD
    (by simpa [mu] using hsum)
  simpa [triangularOuterInnerDenom, mu, M, D] using hmain


theorem triangular_outer_inner_differential_logistic
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    triangularOuterInnerTheta q beta n *
        (1 - triangularOuterInnerTheta q beta n) /
          triangularOuterInnerDenom n q beta ≤
      triangularOuterInnerThetaPrime n q beta := by
  letI : Nonempty (triangularBoxGraph (2 * n)).edgeSet :=
    triangularBoxGraph_edgeSet_nonempty (2 * n) (by omega)
  let G := triangularBoxGraph (2 * n)
  let C := triangularBoxBoundaryGraph (2 * n)
  let J : Sym2 (TriangularBoxVertex (2 * n)) → Real := fun _ => 1
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  let f := triangularInnerCrossInd n
  have hJ : ∀ e, 0 < J e := fun _ => by simp [J]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hcov : Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) /
        triangularOuterInnerDenom n q beta ≤
      ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
    simpa [G, C, J, mu, f] using
      triangular_outer_inner_hcov_geom n hn q beta hq hbeta
  have hpos : ∀ omega, 0 < mu omega :=
    FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    FK.activeBCProb_FKGLatticeCondition G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq
  have hf : Monotone f := triangularInnerCrossInd_monotone n
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
  simpa [triangularOuterInnerTheta, triangularOuterInnerThetaPrime,
    hn0, G, C, J, mu, f] using hmain

end StatMech.FK.PeriodicPlanar
