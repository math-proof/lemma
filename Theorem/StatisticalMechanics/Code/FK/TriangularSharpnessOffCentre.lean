/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
import Def.StatisticalMechanics.Code.FK.TriangularSharpnessOffCentre
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.RevealmentTranslation

theorem triangularBox_reachOpen_hits_centered
    {n m : Nat} {omega : ConfigSpace (triangularBoxGraph n).edgeSet}
    {x b : TriangularBoxVertex n}
    (hreach : ReachOpen (triangularBoxEndU n) (triangularBoxEndV n) omega x b)
    (hm : m ≤ centeredRadius x.1 b.1) :
    ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega x
      (triangularBoxCenteredShell n x m) := by
  by_cases hm0 : m = 0
  · subst m
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, centeredRadius_self x.1⟩,
      ReachOpen.refl x⟩
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hbOuter : b.1 - x.1 ∉ box 2 (m - 1) := by
    intro hb
    have hbRad : centeredRadius x.1 b.1 ≤ m - 1 := by
      rw [mem_box_iff_siteRadius_le] at hb
      simpa [centeredRadius, siteRadius, Pi.sub_apply] using hb
    omega
  have hxInner : x.1 - x.1 ∈ box 2 (m - 1) := by simp
  have hfirst : ∀ {a b : TriangularBoxVertex n},
      ReachOpen (triangularBoxEndU n) (triangularBoxEndV n) omega a b →
      a.1 - x.1 ∈ box 2 (m - 1) → b.1 - x.1 ∉ box 2 (m - 1) →
      ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega a
        (triangularBoxCenteredShell n x m) := by
    intro a b hr
    induction hr with
    | refl a => intro ha hnot; exact (hnot ha).elim
    | @step a y z e hopen hpair hrest ih =>
        intro ha hz
        have hay : (triangularBoxGraph n).Adj a y := by
          rcases hpair with hpair | hpair
          · rw [← hpair.1, ← hpair.2]
            exact triangularBox_end_adj n e
          · rw [← hpair.1, ← hpair.2]
            exact (triangularBox_end_adj n e).symm
        by_cases hy : y.1 - x.1 ∈ box 2 (m - 1)
        · obtain ⟨w, hw, hwy⟩ := ih hy hz
          exact ⟨w, hw, ReachOpen.step e hopen hpair hwy⟩
        · have hadjSub : triangularGraph.Adj (a.1 - x.1) (y.1 - x.1) :=
            triangular_adj_sub_right x.1 hay
          have hym : y.1 - x.1 ∈ box 2 m :=
            triangular_adj_mem_box_of_mem_pred hm1 ha hadjSub
          have hyrad : centeredRadius x.1 y.1 = m := by
            have hym' : siteRadius (y.1 - x.1) ≤ m :=
              mem_box_iff_siteRadius_le.mp hym
            have hy' : ¬ siteRadius (y.1 - x.1) ≤ m - 1 := fun hle =>
              hy (mem_box_iff_siteRadius_le.mpr hle)
            change siteRadius (fun i => y.1 i - x.1 i) = m
            simpa only [Pi.sub_apply] using (show siteRadius (y.1 - x.1) = m by omega)
          refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyrad⟩,
            ReachOpen.step e hopen hpair (ReachOpen.refl y)⟩
  exact hfirst hreach hxInner hbOuter

theorem triangularBox_rootShell_imp_centered_of_le
    {n k m : Nat} {omega : ConfigSpace (triangularBoxGraph n).edgeSet}
    {x : TriangularBoxVertex n}
    (hm : m ≤ ((k : Int) - (siteRadius x.1 : Int)).natAbs) :
    ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega x
        (triangularBoxShell n k) →
      ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega x
        (triangularBoxCenteredShell n x m) := by
  rintro ⟨b, hb, hreach⟩
  have hrb : siteRadius b.1 = k := by
    exact siteRadius_eq_of_mem_vertexBoundary (Finset.mem_filter.mp hb).2
  have htri1 := siteRadius_triangle b.1 x.1
  have htri2 := siteRadius_triangle x.1 b.1
  rw [centeredRadius_comm b.1 x.1] at htri2
  have hdist : ((k : Int) - (siteRadius x.1 : Int)).natAbs ≤
      centeredRadius x.1 b.1 := by
    rw [hrb] at htri1 htri2
    by_cases h : siteRadius x.1 ≤ k
    · have habs : ((k : Int) - (siteRadius x.1 : Int)).natAbs =
          k - siteRadius x.1 := by omega
      rw [habs]
      omega
    · have habs : ((k : Int) - (siteRadius x.1 : Int)).natAbs =
          siteRadius x.1 - k := by omega
      rw [habs]
      omega
  exact triangularBox_reachOpen_hits_centered hreach (hm.trans hdist)


theorem triangular_rootShell_sum_le_centered_sup
    (n : Nat) (mu : ConfigSpace (triangularBoxGraph (2 * n)).edgeSet → Real)
    (hmu0 : ∀ omega, 0 ≤ mu omega) (u : TriangularBoxVertex n) :
    (∑ k : ↑(Finset.Icc 1 n),
      Lindeberg.mean mu (fun omega => if ConnOpenSet
        (triangularBoxEndU n) (triangularBoxEndV n)
        (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
        u (triangularBoxShell n k) then (1 : Real) else 0)) ≤
      2 * (Finset.univ : Finset (TriangularBoxVertex n)).sup'
        ⟨triangularBoxRoot n, Finset.mem_univ _⟩
        (fun x => ∑ j ∈ Finset.range n,
          Lindeberg.mean mu (fun omega => if ConnOpenSet
            (triangularBoxEndU n) (triangularBoxEndV n)
            (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
            x (triangularBoxCenteredShell n x j) then (1 : Real) else 0)) := by
  let conn : TriangularBoxVertex n → Nat → Real := fun x j =>
    Lindeberg.mean mu (fun omega => if ConnOpenSet
      (triangularBoxEndU n) (triangularBoxEndV n)
      (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
      x (triangularBoxCenteredShell n x j) then (1 : Real) else 0)
  let qf : Nat → Real := fun k =>
    Lindeberg.mean mu (fun omega => if ConnOpenSet
      (triangularBoxEndU n) (triangularBoxEndV n)
      (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
      u (triangularBoxShell n k) then (1 : Real) else 0)
  have hconn0 : ∀ x j, 0 ≤ conn x j := fun x j => mean_indicator_nonneg hmu0 _
  have hrn : siteRadius u.1 ≤ n := mem_box_iff_siteRadius_le.mp u.2
  change (∑ k : ↑(Finset.Icc 1 n), qf k) ≤
    2 * (Finset.univ : Finset (TriangularBoxVertex n)).sup'
      ⟨triangularBoxRoot n, Finset.mem_univ _⟩
      (fun x => ∑ j ∈ Finset.range n, conn x j)
  rw [Finset.sum_coe_sort]
  by_cases hr0 : siteRadius u.1 = 0
  · have hcomp0 : ∀ k, 1 ≤ k → qf k ≤ conn u (k - 1) := by
      intro k hk
      apply mean_indicator_mono hmu0
      intro omega homega
      have hm : k - 1 ≤ ((k : Int) - (siteRadius u.1 : Int)).natAbs := by
        rw [hr0]
        simp
      exact triangularBox_rootShell_imp_centered_of_le hm homega
    have hsum : (∑ k ∈ Finset.Icc 1 n, qf k) ≤
        ∑ j ∈ Finset.range n, conn u j := by
      calc
        _ ≤ ∑ k ∈ Finset.Icc 1 n, conn u (k - 1) :=
          Finset.sum_le_sum fun k hk => hcomp0 k (Finset.mem_Icc.mp hk).1
        _ = _ := sum_Icc_one_pred_eq_sum_range (conn u) n
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range n, conn u j :=
      Finset.sum_nonneg fun j _ => hconn0 u j
    have hsup := Finset.le_sup'
      (fun x => ∑ j ∈ Finset.range n, conn x j) (Finset.mem_univ u)
    linarith
  · have hr1 : 1 ≤ siteRadius u.1 := Nat.one_le_iff_ne_zero.mpr hr0
    apply revealment_sum_bound_range (Finset.univ : Finset (TriangularBoxVertex n))
      ⟨triangularBoxRoot n, Finset.mem_univ _⟩ conn hconn0 n
      (siteRadius u.1) hr1 hrn u (Finset.mem_univ u) qf
    intro k
    apply mean_indicator_mono hmu0
    intro omega homega
    exact triangularBox_rootShell_imp_centered_of_le le_rfl homega

end StatMech.FK.PeriodicPlanar
