/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.SLE.Defs.Part4
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

lemma hasHalfPlaneCapacity_id : HasHalfPlaneCapacity id 0 := by
  refine ⟨?_, ?_⟩
  · have : (fun z : ℂ => id z - z) = fun _ => (0 : ℂ) := by funext z; simp
    rw [this]; exact tendsto_const_nhds
  · have : (fun z : ℂ => z * (id z - z)) = fun _ => (0 : ℂ) := by funext z; simp
    rw [this, Complex.ofReal_zero]; exact tendsto_const_nhds


lemma HasHalfPlaneCapacity.unique {g : ℂ → ℂ} {a b : ℝ}
    (ha : HasHalfPlaneCapacity g a) (hb : HasHalfPlaneCapacity g b) : a = b := by
  have hne : (Filter.cocompact ℂ).NeBot := inferInstance
  have := tendsto_nhds_unique ha.2 hb.2
  exact_mod_cast this


end StatMech.SLE
