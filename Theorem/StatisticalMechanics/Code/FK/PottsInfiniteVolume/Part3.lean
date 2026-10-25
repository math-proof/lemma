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
import Def.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part2
open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal


namespace StatMech

namespace FK

open Lattice


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ivp_freeJointPMF_map_fst (q : ℕ) [NeZero q] (beta J : ℝ)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    (ivp_freeJointPMF G q hp hp1
      (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).map Prod.fst =
      Potts.pottsPMF G q beta J := by
  ext s
  rw [PMF.map_apply, Potts.pottsPMF_apply, tsum_fintype]
  simp only [ivp_freeJointPMF, PMF.ofFintype_apply]
  rw [Fintype.sum_prod_type]
  classical
  rw [Finset.sum_eq_single s]
  · simp only [if_pos]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [← esFirstMarginal_eq_pottsProb G q beta J]
      unfold esFirstMarginal ivp_freeJointProb
      rw [Finset.sum_div]
    · intro w _
      exact ivp_freeJointProb_nonneg G hp.le hp1.le (s, w)
  · intro t _ hts
    simp [Ne.symm hts]
  · simp


theorem ivp_freeJointPMF_map_snd (q : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : ℝ)) :
    (ivp_freeJointPMF G q hp hp1 hq).map Prod.snd = fkPMF G hp hp1 hq := by
  ext w
  rw [PMF.map_apply, fkPMF_apply, tsum_fintype]
  simp only [ivp_freeJointPMF, PMF.ofFintype_apply]
  rw [Fintype.sum_prod_type]
  classical
  change (∑ s : V → Fin q, ∑ z : ConfigSpace (Sym2 V),
      if w = z then ENNReal.ofReal (ivp_freeJointProb G q p (s, z)) else 0) = _
  rw [Finset.sum_comm, Finset.sum_eq_single w]
  · simp only [if_pos]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [← esSecondMarginal_eq_fkProb G q p]
      unfold esSecondMarginal ivp_freeJointProb
      rw [Finset.sum_div]
    · intro s _
      exact ivp_freeJointProb_nonneg G hp.le hp1.le (s, w)
  · intro z _ hzw
    simp [Ne.symm hzw]
  · simp


end FK
end StatMech
