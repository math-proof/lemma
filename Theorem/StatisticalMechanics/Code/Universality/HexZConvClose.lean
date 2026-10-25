/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexZConvClose


namespace StatMech.Universality

open scoped BigOperators

open HexWalk


theorem hzc_truncSet_finite (a : ℂ) (h0 : ℤ) (N : ℕ) :
    (hzc_truncSet a h0 N).Finite := by
  apply Set.Finite.subset
    ((List.finite_length_le Bool N).image
      (fun l => l.map (fun b => if b then (1 : ℤ) else -1)))
  rintro ts ⟨hleg, hlen⟩
  have hlen' : ts.length < N := by
    have h1 : (ofTurns a h0 ts).numVertices = ts.length + 1 := by
      rw [numVertices_eq]; rfl
    omega
  refine ⟨ts.map (fun t => decide (t = 1)), ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, List.length_map]; omega
  · simp only [List.map_map]
    conv_rhs => rw [← List.map_id ts]
    apply List.map_congr_left
    intro t ht
    have hmem := hleg.1 t (by simpa [ofTurns] using ht)
    rcases hmem with h | h <;> simp [h]


end StatMech.Universality
