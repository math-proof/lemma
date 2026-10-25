/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc2_engine
import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinpendant
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinconn
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinthickdichotomy.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc_core
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Def.StatisticalMechanics.Code.Walls.jc2_core.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc2_pendantClip_card_lt (K : Set (Site 2)) (hK : K.Finite) (r : Site 2)
    (hr : r ∈ K) : (K \ {r}).ncard < K.ncard := by
  have hsub : (K \ {r}) ⊂ K := by
    rw [Set.ssubset_iff_of_subset Set.diff_subset]
    exact ⟨r, hr, by simp⟩
  exact Set.ncard_lt_ncard hsub hK


theorem jc2_contraction_of_pendantClipMatch (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) (hr : r ∈ K)
    (h : jc2_PendantClipMatch K a r) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
  obtain ⟨hne', a', m, m', n, hp, hp', hmatch, hbal⟩ := h
  refine ⟨K \ {r}, hK.subset Set.diff_subset, hne', a',
    jc2_pendantClip_card_lt K hK r hr, ?_⟩
  rw [cornerBalance_eq_totalTurnZ, cornerBalance_eq_totalTurnZ, hp, hp']
  exact jc2_engine K (K \ {r}) a.1 a'.1 m m' n hmatch hbal


end Walls
end StatMech
