/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Def.StatisticalMechanics.Code.Walls.jc_toprowrun.Part2
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc_zero_mem_runLengths (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K) :
    0 ∈ jc_RunLengths K c := by
  intro j hj
  interval_cases j
  rw [Nat.cast_zero, jc_shiftX_zero]
  exact hc


theorem jc_runLengths_bddAbove (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) :
    BddAbove (jc_RunLengths K c) := by
  classical
  have himg : (((fun v => v 0) '' K)).Finite := hK.image _
  obtain ⟨M, hM⟩ := himg.bddAbove
  refine ⟨(M - c 0).toNat, ?_⟩
  intro n hn
  have hmem : jc_shiftX c (n : ℤ) ∈ K := hn n (le_refl n)
  have hle : (jc_shiftX c (n : ℤ)) 0 ≤ M := hM ⟨_, hmem, rfl⟩
  rw [jc_shiftX_coord0] at hle
  omega


end Walls
end StatMech
