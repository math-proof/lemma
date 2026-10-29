/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Def.StatisticalMechanics.Code.RSW.SelfDualityNode.Part5
open scoped BigOperators ENNReal NNReal
open MeasureTheory


namespace StatMech

namespace RSW

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in


theorem rsd_edgeProduct_compl (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    FK.edgeProduct G p (rsd_edgeCompl ω) = FK.edgeProduct G (1 - p) ω := by
  unfold FK.edgeProduct rsd_edgeCompl
  apply Finset.prod_congr rfl
  intro e _
  cases ω e <;> simp


theorem rsd_fkZ_q1_dual (p : ℝ) : FK.fkZ G p 1 = FK.fkZ G (1 - p) 1 := by
  rw [FK.fkZ_one, FK.fkZ_one,
    ← Equiv.sum_comp (rsd_edgeComplEquiv (V := V)) (fun ω => FK.edgeProduct G p ω)]
  apply Finset.sum_congr rfl
  intro ω _
  exact rsd_edgeProduct_compl G p ω


theorem rsd_fkProb_q1_dual (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    FK.fkProb G p 1 (rsd_edgeCompl ω) = FK.fkProb G (1 - p) 1 ω := by
  unfold FK.fkProb
  rw [FK.fkWeight_one, FK.fkWeight_one, rsd_edgeProduct_compl, rsd_fkZ_q1_dual]


theorem rsd_fkLaw_q1_dual (p : ℝ) (A : Finset (ConfigSpace (Sym2 V))) :
    ∑ ω ∈ A.map (rsd_edgeComplEquiv (V := V)).toEmbedding, FK.fkProb G p 1 ω
      = ∑ ω ∈ A, FK.fkProb G (1 - p) 1 ω := by
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro ω _
  exact rsd_fkProb_q1_dual G p ω


theorem rsd_fkSelfDual_half (ω : ConfigSpace (Sym2 V)) :
    FK.fkProb G (1 / 2) 1 (rsd_edgeCompl ω) = FK.fkProb G (1 / 2) 1 ω := by
  rw [rsd_fkProb_q1_dual]; norm_num


theorem rsd_fkLaw_selfDual_half (A : Finset (ConfigSpace (Sym2 V))) :
    ∑ ω ∈ A.map (rsd_edgeComplEquiv (V := V)).toEmbedding, FK.fkProb G (1 / 2) 1 ω
      = ∑ ω ∈ A, FK.fkProb G (1 / 2) 1 ω := by
  have h := rsd_fkLaw_q1_dual G (1 / 2 : ℝ) A
  rwa [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h


theorem rsd_selfDualPoint_one : rsd_selfDualPoint 1 = 1 / 2 := by
  unfold rsd_selfDualPoint
  rw [Real.sqrt_one]; norm_num


theorem rsd_planarDual_law (p : NNReal) (hp : p ≤ 1) :
    Measure.map Lattice.dualConfig (bernoulliProductMeasure p hp)
      = bernoulliProductMeasure (1 - p) tsub_le_self :=
  Universality.map_dualConfig p hp


theorem rsd_planarDual_selfDual_half :
    Measure.map Lattice.dualConfig
        (bernoulliProductMeasure (2⁻¹ : NNReal) Universality.half_le_one)
      = bernoulliProductMeasure (2⁻¹ : NNReal) Universality.half_le_one :=
  Universality.bernoulliProductMeasure_selfDual_half


theorem rsd_planarDual_invol (p : NNReal) (hp : p ≤ 1) :
    Measure.map Lattice.dualConfig
        (Measure.map Lattice.dualConfig (bernoulliProductMeasure p hp))
      = bernoulliProductMeasure p hp :=
  Universality.map_dualConfig_dualConfig p hp


end RSW
end StatMech
