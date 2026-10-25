/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle.Part3
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2
import Def.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part2


namespace StatMech.Onsager

open BigOperators

@[simp] theorem ons_spinSeamDecWeight_external
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (d : ons_Dart L) :
    ons_spinSeamDecWeight decWeight a b s(d, ons_dartRev L d) =
      ons_spinDartSeamSign a b d *
        decWeight s(d, ons_dartRev L d) := by
  classical
  unfold ons_spinSeamDecWeight
  split_ifs with h
  · let chosen := Classical.choose h
    have hchosen : s(d, ons_dartRev L d) =
        s(chosen, ons_dartRev L chosen) := Classical.choose_spec h
    have hor : chosen = d ∨ chosen = ons_dartRev L d :=
      (ons_externalDecoratedEdge_eq_iff L d chosen).mp hchosen.symm
    change ons_spinDartSeamSign a b chosen *
      decWeight s(d, ons_dartRev L d) = _
    rcases hor with heq | hrev
    · rw [heq]
    · rw [hrev, ons_spinDartSeamSign_rev]
  · exact (h ⟨d, rfl⟩).elim

@[simp] theorem ons_spinSeamDecWeight_chain
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (site : ZMod L × ZMod L) (i : Fin 3) :
    ons_spinSeamDecWeight decWeight a b (ons_decChainEdge site i) =
      decWeight (ons_decChainEdge site i) := by
  classical
  unfold ons_spinSeamDecWeight
  rw [dif_neg (ons_decChainEdge_not_external L site i)]

end StatMech.Onsager
