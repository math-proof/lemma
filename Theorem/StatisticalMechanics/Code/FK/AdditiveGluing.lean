/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
import Theorem.StatisticalMechanics.Code.FK.GenuineEdgeCollapse
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Instance.StatisticalMechanics.Code.FK.AdditiveGluing.Part2
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

section Partition

variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]
  (P : U → Prop) [DecidablePred P]


@[simp] theorem agl_sumEquiv_inl (a : {x // P x}) :
    agl_sumEquiv P (Sum.inl a) = (a : U) := rfl

@[simp] theorem agl_sumEquiv_inr (b : {x // ¬ P x}) :
    agl_sumEquiv P (Sum.inr b) = (b : U) := rfl

@[simp] theorem agl_glueGraph_adj (u v : {x // P x} ⊕ {x // ¬ P x}) :
    (agl_glueGraph K₀ P).Adj u v ↔ K₀.Adj (agl_sumEquiv P u) (agl_sumEquiv P v) := by
  unfold agl_glueGraph
  rw [comap_adj]


theorem agl_partitionCrossInterface :
    fis_CrossInterface (agl_left K₀ P) (agl_right K₀ P) (agl_glueGraph K₀ P) := by
  refine ⟨?_, ?_, ?_⟩
  · 
    intro u v huv
    rw [agl_glueGraph_adj]
    match u, v, huv with
    | Sum.inl a, Sum.inl b, huv =>
      rw [SimpleGraph.sum_adj] at huv
      
      simpa [agl_left, comap_adj] using huv
    | Sum.inr c, Sum.inr e, huv =>
      rw [SimpleGraph.sum_adj] at huv
      simpa [agl_right, comap_adj] using huv
    | Sum.inl a, Sum.inr e, huv => simp only [SimpleGraph.sum_adj] at huv
    | Sum.inr c, Sum.inl b, huv => simp only [SimpleGraph.sum_adj] at huv
  · 
    intro a b hab
    rw [agl_glueGraph_adj] at hab
    simpa [agl_left, comap_adj] using hab
  · 
    intro c e hce
    rw [agl_glueGraph_adj] at hce
    simpa [agl_right, comap_adj] using hce


end Partition
end FK
end StatMech
