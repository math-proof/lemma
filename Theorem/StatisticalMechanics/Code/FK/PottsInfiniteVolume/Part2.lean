/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsLatticeBridge
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
import Def.StatisticalMechanics.Code.FK.PottsInfiniteVolume
open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal


namespace StatMech

namespace FK

open Lattice


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ivp_freeJointProb_nonneg {q : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (z : (V → Fin q) × ConfigSpace (Sym2 V)) : 0 ≤ ivp_freeJointProb G q p z := by
  apply div_nonneg (esWeight_nonneg G hp hp1 z.1 z.2)
  exact Finset.sum_nonneg fun w _ =>
    Finset.sum_nonneg fun s _ => esWeight_nonneg G hp hp1 s w


theorem ivp_freeJointProb_eq_fkProb_div_pow {q : Nat} {p : Real}
    (hq : 0 < (q : Real))
    (sigma : V -> Fin q) (omega : ConfigSpace (Sym2 V)) :
    ivp_freeJointProb G q p (sigma, omega) =
      if ConstOnOpen G omega sigma then
        fkProb G p (q : Real) omega / (q : Real) ^ numClusters G omega
      else 0 := by
  unfold ivp_freeJointProb
  rw [esWeight_factor, monoProd_eq_indicator, esZ_eq_fkZ]
  by_cases hconst : ConstOnOpen G omega sigma
  · rw [if_pos hconst, if_pos hconst]
    unfold fkProb fkWeight
    have hpow : (q : Real) ^ numClusters G omega ≠ 0 :=
      pow_ne_zero _ hq.ne'
    field_simp
  · rw [if_neg hconst, if_neg hconst]
    simp

theorem ivp_freeJointProb_sum_eq_one {q : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : ℝ)) :
    ∑ z : (V → Fin q) × ConfigSpace (Sym2 V), ivp_freeJointProb G q p z = 1 := by
  unfold ivp_freeJointProb
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_div]
  rw [show (∑ s : V → Fin q, ∑ w : ConfigSpace (Sym2 V), esWeight G p s w) =
      esZ G q p by rw [esZ, Finset.sum_comm]]
  exact div_self (esZ_pos G hp hp1 hq).ne'


end FK
end StatMech
