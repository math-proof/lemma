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
import Def.StatisticalMechanics.Code.Universality.HexSurgerySeams


namespace StatMech.Universality

open Complex HexWalk List Filter

open scoped Topology BigOperators


theorem hexCut_legal_drop (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ) (hcp : cp ≤ ts.length)
    (hleg : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns (hexDropMid a h0 ts cp) (h0 + (ts.take cp).sum) (ts.drop cp)).IsLegalSAW := by
  obtain ⟨hturns, hsaw⟩ := hleg
  refine ⟨fun t ht => hturns t (List.mem_of_mem_drop ht), ?_⟩
  unfold IsSAW vertices ofTurns at hsaw ⊢
  simp only at hsaw ⊢
  unfold hexDropMid
  rw [dif_pos hcp, ← (hexVerticesAux_drop a h0 ts cp hcp).choose_spec]
  exact hsaw.sublist (List.drop_sublist cp _)


end StatMech.Universality
