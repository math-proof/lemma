/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TopRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCrossing.Part4
import Def.StatisticalMechanics.Code.Onsager.UmlaufsatzStrip
import Def.StatisticalMechanics.Code.Onsager.TopRow


namespace StatMech.Onsager.TopRow

open Finset

open Fin.NatCast

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

open StatMech.Onsager.WalkCrossing

variable {n : ℕ} [NeZero n]


theorem topRowContiguous_of_singleTopRun (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    {M : Fin n} (hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2)
    (hrun : SingleTopRun d M) :
    StatMech.Onsager.UmlaufsatzStrip.TopRowContiguous d := by
  refine ⟨M, hmax, ?_⟩
  intro a b ha hb x hax hxb
  
  obtain ⟨ja, hja, hxa⟩ := hrun a ha
  obtain ⟨jb, hjb, hxb'⟩ := hrun b hb
  
  set xM : ℤ := (pos d M).1 with hxM
  
  have hx_le_xM : x ≤ xM := le_trans hxb (by rw [hxb']; omega)
  set j : ℕ := (xM - x).toNat with hjdef
  have hjcast : (j : ℤ) = xM - x := by rw [hjdef]; omega
  
  have hj_le_ja : j ≤ ja := by
    have h1 : (j : ℤ) ≤ (ja : ℤ) := by rw [hjcast]; omega
    exact_mod_cast h1
  have hjprefix : ∀ i : ℕ, i < j → d (M + (Nat.cast i : Fin n)) = 2 :=
    fun i hi => hja i (lt_of_lt_of_le hi hj_le_ja)
  
  refine ⟨M + (Nat.cast j : Fin n), ?_⟩
  rw [forward_west_run d hclosed M j hjprefix]
  ext
  · show (pos d M).1 - (j : ℤ) = x; rw [hjcast]; ring
  · rfl


theorem topRowContiguous_of_residue (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (hres : ∀ M : Fin n, d (M - 1) = 1 → d M = 2 →
      (∀ j : Fin n, (pos d j).2 ≤ (pos d M).2) → SingleTopRun d M) :
    StatMech.Onsager.UmlaufsatzStrip.TopRowContiguous d := by
  obtain ⟨M, hin, hout, hmax, _hright⟩ :=
    StatMech.Onsager.UmlaufsatzStrip.ymax_NW_corner d hclosed hreflexfree
  exact topRowContiguous_of_singleTopRun d hclosed hmax (hres M hin hout hmax)

end StatMech.Onsager.TopRow
