/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain
open scoped BigOperators Classical
open Finset Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


theorem bcWeightW_pos {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    0 < bcWeightW G C pf q omega := by
  exact mul_pos (edgeProductW_pos G hpf hpf1 omega) (pow_pos hq _)

theorem bcWeightW_nonneg {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    0 <= bcWeightW G C pf q omega :=
  (bcWeightW_pos G C hpf hpf1 hq omega).le

theorem bcZW_pos {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) : 0 < bcZW G C pf q := by
  unfold bcZW
  exact Finset.sum_pos (fun omega _ => bcWeightW_pos G C hpf hpf1 hq omega)
    Finset.univ_nonempty

theorem bcProbW_nonneg {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    0 <= bcProbW G C pf q omega := by
  exact div_nonneg (bcWeightW_nonneg G C hpf hpf1 hq omega)
    (bcZW_pos G C hpf hpf1 hq).le

theorem bcProbW_sum_eq_one {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) :
    ∑ omega, bcProbW G C pf q omega = 1 := by
  unfold bcProbW bcZW
  rw [← Finset.sum_div]
  exact div_self (bcZW_pos G C hpf hpf1 hq).ne'


theorem bcWeightW_cross_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (a b : ConfigSpace (Sym2 V)) :
    bcWeightW G C pf q a * bcWeightW G C' pf q b <=
      bcWeightW G C pf q (a ⊓ b) * bcWeightW G C' pf q (a ⊔ b) := by
  have hcluster :
      q ^ numClustersBC G C a * q ^ numClustersBC G C' b <=
        q ^ numClustersBC G C (a ⊓ b) *
          q ^ numClustersBC G C' (a ⊔ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hq (mixed_supermodular_bc G C C' hCC' a b)
  have hedge := edgeProductW_logModular G pf a b
  have hedge0 : 0 <=
      edgeProductW G pf (a ⊓ b) * edgeProductW G pf (a ⊔ b) :=
    mul_nonneg (edgeProductW_pos G hpf hpf1 _).le
      (edgeProductW_pos G hpf hpf1 _).le
  unfold bcWeightW
  calc
    (edgeProductW G pf a * q ^ numClustersBC G C a) *
          (edgeProductW G pf b * q ^ numClustersBC G C' b) =
        (edgeProductW G pf a * edgeProductW G pf b) *
          (q ^ numClustersBC G C a * q ^ numClustersBC G C' b) := by ring
    _ = (edgeProductW G pf (a ⊓ b) * edgeProductW G pf (a ⊔ b)) *
          (q ^ numClustersBC G C a * q ^ numClustersBC G C' b) := by
        rw [hedge]
        ring
    _ <= (edgeProductW G pf (a ⊓ b) * edgeProductW G pf (a ⊔ b)) *
          (q ^ numClustersBC G C (a ⊓ b) *
            q ^ numClustersBC G C' (a ⊔ b)) :=
        mul_le_mul_of_nonneg_left hcluster hedge0
    _ = (edgeProductW G pf (a ⊓ b) *
          q ^ numClustersBC G C (a ⊓ b)) *
        (edgeProductW G pf (a ⊔ b) *
          q ^ numClustersBC G C' (a ⊔ b)) := by ring

theorem bcProbW_cross_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (a b : ConfigSpace (Sym2 V)) :
    bcProbW G C pf q a * bcProbW G C' pf q b <=
      bcProbW G C pf q (a ⊓ b) * bcProbW G C' pf q (a ⊔ b) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hZ : 0 < bcZW G C pf q := bcZW_pos G C hpf hpf1 hq0
  have hZ' : 0 < bcZW G C' pf q := bcZW_pos G C' hpf hpf1 hq0
  unfold bcProbW
  rw [div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff_of_pos_right (mul_pos hZ hZ')]
  exact bcWeightW_cross_bc G C C' hCC' hpf hpf1 hq a b


theorem bcProbW_mono_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW G C pf q omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW G C' pf q omega := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun omega => bcProbW_nonneg G C hpf hpf1 hq0 omega
  · exact fun omega => bcProbW_nonneg G C' hpf hpf1 hq0 omega
  · rw [bcProbW_sum_eq_one G C hpf hpf1 hq0,
      bcProbW_sum_eq_one G C' hpf hpf1 hq0]
  · exact fun a b => bcProbW_cross_bc G C C' hCC' hpf hpf1 hq a b


end FK
end StatMech
