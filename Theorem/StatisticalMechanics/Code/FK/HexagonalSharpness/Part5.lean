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
import Def.StatisticalMechanics.Code.FK.HexagonalSharpness.Part6
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

theorem hexagonalBox_differential_inequality
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0) :
    ∃ c : Real, 0 < c ∧
      c * (hexagonalBoxCrossMass n q beta /
        hexagonalBoxDenom n q beta) ≤
      deriv (hexagonalBoxCrossMass n q) beta := by
  letI : Nonempty (hexagonalBoxGraph n).edgeSet :=
    hexagonalBoxGraph_edgeSet_nonempty n hn
  letI : Nonempty (HexagonalBoxVertex n) := ⟨hexagonalBoxRoot n⟩
  let mu := FK.activeBCProb (hexagonalBoxGraph n)
    (hexagonalBoxBoundaryGraph n) (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩ (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalBoxConnMass n q beta x k)
  let D := 2 * (1 + M) / (n : Real)
  have hconn0 : ∀ x k, 0 ≤ hexagonalBoxConnMass n q beta x k := by
    intro x k
    unfold hexagonalBoxConnMass Lindeberg.mean
    exact Finset.sum_nonneg fun omega _ => mul_nonneg (by
      change 0 ≤ if ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n)
        omega x (hexagonalBoxShell n k) then (1 : Real) else 0
      split_ifs <;> norm_num)
        (FK.activeBCProb_pos (hexagonalBoxGraph n) (hexagonalBoxBoundaryGraph n)
          (FK.betaParams_pos (fun _ => by norm_num) hbeta)
          (FK.betaParams_lt_one (fun _ => 1) beta)
          (zero_lt_one.trans_le hq) omega).le
  have hM : 0 ≤ M := by
    let x : HexagonalBoxVertex n := hexagonalBoxRoot n
    have hx : x ∈ (Finset.univ : Finset (HexagonalBoxVertex n)) := Finset.mem_univ _
    have hx0 : 0 ≤ ∑ k : ↑(Finset.Icc 1 n),
        hexagonalBoxConnMass n q beta x k :=
      Finset.sum_nonneg fun k _ => hconn0 x k
    exact hx0.trans
      (Finset.le_sup' (fun y => ∑ k : ↑(Finset.Icc 1 n),
        hexagonalBoxConnMass n q beta y k) hx)
  have hnR : 0 < (n : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hD : 0 < D := by dsimp [D]; positivity
  have hsum : ∀ e : (hexagonalBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean mu (fun omega => if ConnOpenSet
          (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega
          (hexagonalBoxEndU n e) (hexagonalBoxShell n k) then 1 else 0) +
        Lindeberg.mean mu (fun omega => if ConnOpenSet
          (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega
          (hexagonalBoxEndV n e) (hexagonalBoxShell n k) then 1 else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
    intro e
    have hu := Finset.le_sup' (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalBoxConnMass n q beta x k)
      (Finset.mem_univ (hexagonalBoxEndU n e))
    have hv := Finset.le_sup' (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalBoxConnMass n q beta x k)
      (Finset.mem_univ (hexagonalBoxEndV n e))
    have hcard : (Fintype.card (↑(Finset.Icc 1 n)) : Real) = n := by
      rw [Fintype.card_coe, Nat.card_Icc]
      norm_num
    rw [Finset.sum_add_distrib]
    change
      (∑ k : ↑(Finset.Icc 1 n),
          hexagonalBoxConnMass n q beta (hexagonalBoxEndU n e) k) +
        (∑ k : ↑(Finset.Icc 1 n),
          hexagonalBoxConnMass n q beta (hexagonalBoxEndV n e) k) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D
    calc
      _ ≤ M + M := add_le_add hu hv
      _ ≤ (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
        rw [hcard]
        dsimp [D]
        rw [mul_div_cancel₀ _ hnR.ne']
        linarith
  obtain ⟨c, hc, hmain⟩ := activeBC_openCross_differential_inequality
    (hexagonalBoxGraph n) (hexagonalBoxBoundaryGraph n) (fun _ => 1)
    (fun _ => by norm_num) q beta beta0 hq hbeta hbeta0
    (hexagonalBoxEndU n) (hexagonalBoxEndV n)
    (hexagonalBox_end_coherent n) (hexagonalBoxRoot n)
    (Finset.univ : Finset (hexagonalBoxGraph n).edgeSet).toList
    (by simp) (hexagonalBoxShell n) (hexagonalBoxShell n)
    (by simp) (by simp) (by
      intro k hk
      simp [hexagonalBoxShell, hexagonalBoxRoot, vertexBoundary] at hk)
    (by
      intro k m hk hkm omega h
      exact hexagonalBox_reachOpen_crosses hk hkm omega h)
    n hn D hD hsum
  refine ⟨c, hc, ?_⟩
  simpa [hexagonalBoxCrossMass, hexagonalBoxDenom, M, D] using hmain

end StatMech.FK.PeriodicPlanar
