/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSignedPhysical.Part5
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem triangularTorusSeamTwistedPartition_eq
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) :
    StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
        (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi) (fun _ => 0) =
      (2 : Real) ^ (L * L) *
        triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
  rw [triangularTorusSeamTwistedPartition_highTemperature]
  unfold triangularTorusNormalizedLinearSector
  ring

theorem triangularTorusNormalizedLinearSector_pos
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) :
    0 < triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
  have hZ := StatMech.Sharpness.ZJ_pos
    (triangularTorusGraph L).edgeFinset
    (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi) (fun _ => 0)
  rw [triangularTorusSeamTwistedPartition_eq] at hZ
  rcases mul_pos_iff.mp hZ with h | h
  · exact h.2
  · exfalso
    exact (not_lt_of_ge (by positivity)) h.1


theorem ZJ_log_coupling_sub_abs_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (J J' : Sym2 V → Real) :
    |Real.log (StatMech.Sharpness.ZJ E J (fun _ => 0)) -
        Real.log (StatMech.Sharpness.ZJ E J' (fun _ => 0))| ≤
      ∑ edge ∈ E, |J edge - J' edge| := by
  let action : (Sym2 V → Real) → ConfigSpace V → Real := fun K s =>
    ∑ edge ∈ E, K edge * bond s edge
  have haction (s : ConfigSpace V) :
      |action J s - action J' s| ≤
        ∑ edge ∈ E, |J edge - J' edge| := by
    dsimp only [action]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ edge ∈ E,
          (J edge * bond s edge - J' edge * bond s edge)| ≤
        ∑ edge ∈ E,
          |J edge * bond s edge - J' edge * bond s edge| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ edge ∈ E, |J edge - J' edge| := by
        apply Finset.sum_le_sum
        intro edge hedge
        rw [← sub_mul, abs_mul]
        have hb : |bond s edge| ≤ 1 := by
          rcases bond_eq_pm s edge with h | h <;> simp [h]
        exact mul_le_of_le_one_right (abs_nonneg _) hb
  have hdist := logZ_dist_le (-1) (action J) (action J')
    (∑ edge ∈ E, |J edge - J' edge|) haction
  simpa [StatMech.Ising.Z, StatMech.Sharpness.ZJ,
    StatMech.Sharpness.wJ, action] using hdist

theorem abs_triangularTorusRealEdgeWeight_le
    (L : Nat) (J1 J2 J3 : Real)
    (edge : Sym2 (ZMod L × ZMod L)) :
    |triangularTorusRealEdgeWeight L J1 J2 J3 edge| ≤
      |J1| + |J2| + |J3| := by
  unfold triangularTorusRealEdgeWeight
  split_ifs <;>
    nlinarith [abs_nonneg J1, abs_nonneg J2, abs_nonneg J3]

theorem abs_triangularTorusSeamTwistedCoupling_sub_le
    (L : Nat) (J1 J2 J3 : Real) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) :
    |triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge -
        triangularTorusRealEdgeWeight L J1 J2 J3 edge| ≤
      2 * (|J1| + |J2| + |J3|) *
        ((if triangularTorusXSeamEdge L edge then 1 else 0) +
          (if triangularTorusYSeamEdge L edge then 1 else 0)) := by
  let S := |J1| + |J2| + |J3|
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hw := abs_triangularTorusRealEdgeWeight_le L J1 J2 J3 edge
  have hflip :
      |-triangularTorusRealEdgeWeight L J1 J2 J3 edge -
          triangularTorusRealEdgeWeight L J1 J2 J3 edge| =
        2 * |triangularTorusRealEdgeWeight L J1 J2 J3 edge| := by
    rw [show -triangularTorusRealEdgeWeight L J1 J2 J3 edge -
        triangularTorusRealEdgeWeight L J1 J2 J3 edge =
      -(2 * triangularTorusRealEdgeWeight L J1 J2 J3 edge) by ring,
      abs_neg, abs_mul]
    norm_num
  rcases chi with ⟨chi1, chi2⟩
  fin_cases chi1 <;> fin_cases chi2 <;>
    simp [triangularTorusSeamTwistedCoupling,
      triangularTorusSeamTwistSign, triangularTorusLinearCharacter] <;>
    split_ifs <;> simp_all [hflip] <;> nlinarith


theorem triangularTorusSeamTwistedPartition_log_sub_abs_le
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) :
    |Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
        (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi) (fun _ => 0)) -
      Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
        (triangularTorusRealEdgeWeight L J1 J2 J3) (fun _ => 0))| ≤
      8 * (|J1| + |J2| + |J3|) * L := by
  calc
    _ ≤ ∑ edge ∈ (triangularTorusGraph L).edgeFinset,
        |triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge -
          triangularTorusRealEdgeWeight L J1 J2 J3 edge| :=
      ZJ_log_coupling_sub_abs_le (triangularTorusGraph L).edgeFinset _ _
    _ ≤ ∑ edge ∈ (triangularTorusGraph L).edgeFinset,
        2 * (|J1| + |J2| + |J3|) *
          ((if triangularTorusXSeamEdge L edge then 1 else 0) +
            (if triangularTorusYSeamEdge L edge then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro edge hedge
      exact abs_triangularTorusSeamTwistedCoupling_sub_le
        L J1 J2 J3 chi edge
    _ = _ := by
      rw [← Finset.mul_sum]
      simp_rw [Finset.sum_add_distrib, Finset.sum_boole]
      rw [triangularTorusXSeamEdge_card,
        triangularTorusYSeamEdge_card]
      push_cast
      ring

@[simp] theorem triangularTorusSeamTwistedCoupling_zero
    (L : Nat) (J1 J2 J3 : Real) :
    triangularTorusSeamTwistedCoupling L J1 J2 J3 (0, 0) =
      triangularTorusRealEdgeWeight L J1 J2 J3 := by
  funext edge
  simp [triangularTorusSeamTwistedCoupling,
    triangularTorusSeamTwistSign, triangularTorusLinearCharacter]

theorem triangularTorusNormalizedLinearSector_zero
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real) :
    triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) =
      (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) *
        inhomogeneousEvenSubgraphSum (triangularTorusGraph L)
          (triangularTorusRealEdgeWeight L
            (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) := by
  unfold triangularTorusNormalizedLinearSector
    triangularTorusWeightedLinearCharacterSum
    inhomogeneousEvenSubgraphSum
  congr 1
  apply Finset.sum_congr rfl
  intro F hF
  simp [triangularTorusLinearCharacter]


theorem triangularTorusNormalizedLinearSector_log_sub_abs_le
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) :
    |Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 chi) -
      Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0))| ≤
      8 * (|J1| + |J2| + |J3|) * L := by
  have h := triangularTorusSeamTwistedPartition_log_sub_abs_le
    L J1 J2 J3 chi
  rw [← triangularTorusSeamTwistedCoupling_zero L J1 J2 J3,
    triangularTorusSeamTwistedPartition_eq,
    triangularTorusSeamTwistedPartition_eq] at h
  have hpow : (2 : Real) ^ (L * L) ≠ 0 := by positivity
  have hchi := triangularTorusNormalizedLinearSector_pos L J1 J2 J3 chi
  have hzero := triangularTorusNormalizedLinearSector_pos
    L J1 J2 J3 (0, 0)
  rw [Real.log_mul hpow hchi.ne', Real.log_mul hpow hzero.ne'] at h
  convert h using 1 <;> congr 1 <;> ring

theorem triangularTorusNormalizedLinearSector_le_exp_boundary_mul
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) :
    triangularTorusNormalizedLinearSector L J1 J2 J3 chi ≤
      Real.exp (8 * (|J1| + |J2| + |J3|) * L) *
        triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) := by
  let B : Real := 8 * (|J1| + |J2| + |J3|) * L
  let Pchi := triangularTorusNormalizedLinearSector L J1 J2 J3 chi
  let Pzero := triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)
  have hchi : 0 < Pchi :=
    triangularTorusNormalizedLinearSector_pos L J1 J2 J3 chi
  have hzero : 0 < Pzero :=
    triangularTorusNormalizedLinearSector_pos L J1 J2 J3 (0, 0)
  have habs := triangularTorusNormalizedLinearSector_log_sub_abs_le
    L J1 J2 J3 chi
  have hlog : Real.log Pchi ≤ Real.log Pzero + B := by
    dsimp only [Pchi, Pzero, B] at habs ⊢
    linarith [le_abs_self
      (Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 chi) -
        Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)))]
  calc
    Pchi = Real.exp (Real.log Pchi) := (Real.exp_log hchi).symm
    _ ≤ Real.exp (Real.log Pzero + B) := Real.exp_le_exp.mpr hlog
    _ = Real.exp B * Pzero := by
      rw [Real.exp_add, Real.exp_log hzero]
      ring


end StatMech.FrontierA
