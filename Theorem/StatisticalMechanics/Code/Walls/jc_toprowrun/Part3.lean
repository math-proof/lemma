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
import Def.StatisticalMechanics.Code.Walls.jc_toprowrun.Part3
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc_runMax_mem (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) (hc : c ∈ K) :
    jc_runMax K c ∈ jc_RunLengths K c := by
  apply Nat.sSup_mem
  · exact ⟨0, jc_zero_mem_runLengths K c hc⟩
  · exact jc_runLengths_bddAbove K hK c


theorem jc_runMax_succ_not_mem (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) :
    jc_runMax K c + 1 ∉ jc_RunLengths K c := by
  intro hmem
  have hle : jc_runMax K c + 1 ≤ jc_runMax K c :=
    le_csSup (jc_runLengths_bddAbove K hK c) hmem
  omega


theorem jc_runMax_succ_nmem_K (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) (hc : c ∈ K) :
    jc_shiftX c ((jc_runMax K c : ℤ) + 1) ∉ K := by
  intro hmem
  apply jc_runMax_succ_not_mem K hK c
  intro j hj
  rcases Nat.lt_or_ge j (jc_runMax K c + 1) with h | h
  · exact jc_runMax_mem K hK c hc j (by omega)
  · have hj' : j = jc_runMax K c + 1 := by omega
    subst hj'
    push_cast
    exact hmem


end Walls
end StatMech
