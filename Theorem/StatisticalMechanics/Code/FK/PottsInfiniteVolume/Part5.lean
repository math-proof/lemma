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
import Def.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part4
open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal


namespace StatMech

namespace FK

open Lattice


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


namespace Wired

open IsingFK

variable (bdry : V → Prop) [DecidablePred bdry]


theorem ivp_wiredJointPMF_map_fst {q : ℕ} [NeZero q]
    (b : Fin q) (beta J : ℝ) (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
    (ivp_wiredJointPMF G bdry b beta J hp).map Prod.fst =
      PMF.ofFintype
        (fun s => ENNReal.ofReal (pottsProbWired G bdry q b beta J s)) (by
          rw [← ENNReal.ofReal_sum_of_nonneg
              (fun s _ => pottsProbWired_nonneg G bdry q b beta J s),
            pottsProbWired_sum_eq_one G bdry q b beta J, ENNReal.ofReal_one]) := by
  ext s
  rw [PMF.map_apply, PMF.ofFintype_apply, tsum_fintype]
  simp only [ivp_wiredJointPMF, PMF.ofFintype_apply]
  rw [Fintype.sum_prod_type]
  classical
  rw [Finset.sum_eq_single s]
  · simp only [if_pos]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [← esWiredFirstMarginal_eq_pottsProbWired G bdry b beta J]
      unfold esWiredFirstMarginal ivp_wiredJointProb
      rw [Finset.sum_div]
    · intro w _
      exact ivp_wiredJointProb_nonneg G bdry b beta J hp (s, w)
  · intro t _ hts
    simp [Ne.symm hts]
  · simp


theorem ivp_wiredJointPMF_map_snd {q : ℕ} [NeZero q]
    (b : Fin q) (beta J : ℝ)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1)
    (v0 : V) (hv0 : bdry v0) :
    (ivp_wiredJointPMF G bdry b beta J hp.le).map Prod.snd =
      wiredFkPMF G bdry hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q) := by
  ext w
  rw [PMF.map_apply, wiredFkPMF, PMF.ofFintype_apply, tsum_fintype]
  simp only [ivp_wiredJointPMF, PMF.ofFintype_apply]
  rw [Fintype.sum_prod_type]
  classical
  change (∑ s : V → Fin q, ∑ z : ConfigSpace (Sym2 V),
      if w = z then ENNReal.ofReal (ivp_wiredJointProb G bdry b beta J (s, z)) else 0) = _
  rw [Finset.sum_comm, Finset.sum_eq_single w]
  · simp only [if_pos]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [wiredFkProb_eq_bcProb G bdry]
      rw [← esWiredSecondMarginal_eq_bcProb G bdry b
        (1 - Real.exp (-(beta * J))) w v0 hv0 (Nat.pos_of_neZero q)
        (fun z => one_le_numClustersBC G bdry v0 z)]
      unfold esWiredSecondMarginal ivp_wiredJointProb
      rw [Finset.sum_div]
    · intro s _
      exact ivp_wiredJointProb_nonneg G bdry b beta J hp.le (s, w)
  · intro z _ hzw
    simp [Ne.symm hzw]
  · simp

end Wired
end FK
end StatMech
