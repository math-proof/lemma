/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part3


namespace StatMech.Universality

open Complex HexWalk List Filter

open scoped Topology BigOperators


def hexCanonBridge (T : ℕ) (hT : 0 < T) : HexBridge := ⟨T, hT, [0], by simp⟩


noncomputable def bridgeSeqOfFinset (s : Finset ℕ) (hs : ∀ T ∈ s, 0 < T) : List HexBridge :=
  (s.sort (· ≤ ·)).reverse.pmap (fun T (hT : 0 < T) => hexCanonBridge T hT)
    (by
      intro T hT
      rw [List.mem_reverse, Finset.mem_sort] at hT
      exact hs T hT)


end StatMech.Universality
