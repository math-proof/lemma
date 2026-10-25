/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Def.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


theorem continuous_clampX (a b : ℝ) : Continuous (clampX a b) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [clampX, clampCoord] <;> fun_prop

theorem continuous_clampY (c d : ℝ) : Continuous (clampY c d) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [clampY, clampCoord] <;> fun_prop


theorem strip_paths_intersect
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {hl hr vb vt : Fin 2 → ℝ}
    (gamma : Path hl hr) (eta : Path vb vt)
    (hl0 : hl 0 < a) (hr0 : b < hr 0)
    (vb1 : vb 1 < c) (vt1 : d < vt 1)
    (hgammaY : ∀ t : unitInterval, c < gamma t 1 ∧ gamma t 1 < d)
    (hetaX : ∀ t : unitInterval, a < eta t 0 ∧ eta t 0 < b) :
    ∃ t s : unitInterval, gamma t = eta s := by
  let gamma' := gamma.map (continuous_clampX a b)
  let eta' := eta.map (continuous_clampY c d)
  have hgammaRect : Set.range gamma' ⊆ {x | InRectangle a b c d x} := by
    intro x hx
    obtain ⟨t, rfl⟩ := hx
    have hb := clampCoord_bounds (x := gamma t 0) hab.le
    have hy := hgammaY t
    exact ⟨hb.1, hb.2, hy.1.le, hy.2.le⟩
  have hetaRect : Set.range eta' ⊆ {x | InRectangle a b c d x} := by
    intro x hx
    obtain ⟨t, rfl⟩ := hx
    have hb := clampCoord_bounds (x := eta t 1) hcd.le
    have hx' := hetaX t
    exact ⟨hx'.1.le, hx'.2.le, hb.1, hb.2⟩
  have hgl : (clampX a b hl) 0 = a := by
    simp [clampX, clampCoord_of_le_left hab.le hl0.le]
  have hgr : (clampX a b hr) 0 = b := by
    simp [clampX, clampCoord_of_right_le hab.le hr0.le]
  have hev : (clampY c d vb) 1 = c := by
    simp [clampY, clampCoord_of_le_left hcd.le vb1.le]
  have het : (clampY c d vt) 1 = d := by
    simp [clampY, clampCoord_of_right_le hcd.le vt1.le]
  obtain ⟨t, s, hts⟩ := rectangle_paths_intersect hab hcd gamma' eta'
    hgammaRect hetaRect hgl hgr hev het
  have hxClamp : clampCoord a b (gamma t 0) = eta s 0 := by
    simpa [gamma', eta', clampX, clampY] using congrFun hts 0
  have hyClamp : clampCoord c d (eta s 1) = gamma t 1 := by
    symm
    simpa [gamma', eta', clampX, clampY] using congrFun hts 1
  have hx : gamma t 0 = eta s 0 :=
    eq_of_clampCoord_eq_interior hab (hetaX s).1 (hetaX s).2 hxClamp
  have hy : gamma t 1 = eta s 1 :=
    (eq_of_clampCoord_eq_interior hcd (hgammaY t).1 (hgammaY t).2 hyClamp).symm
  refine ⟨t, s, ?_⟩
  funext i
  fin_cases i
  · simpa using hx
  · simpa using hy

end ContinuousRectangleCrossing
end StatMech
