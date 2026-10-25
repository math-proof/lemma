/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.SharpnessFK
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part7
import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
open scoped BigOperators
open Finset
open Real Set
open StatMech.Lattice

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

open StatMech.OSSS

open StatMech.OSSS.CovLowerBound

open StatMech.OSSS.SharpnessFK

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.TreeComplete

open StatMech.OSSS.DecisionTree

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]


section Lattice

variable {d : ℕ}


theorem liftCfg_monotone (edge : E → Sym2 (Site d)) :
    Monotone (liftCfg edge) := by
  intro ω₁ ω₂ h s
  unfold liftCfg
  by_cases hex : ∃ e, edge e = s
  · rw [dif_pos hex, dif_pos hex]; exact h hex.choose
  · rw [dif_neg hex, dif_neg hex]


theorem openSubgraph_mono {ω₁ ω₂ : ConfigSpace (Sym2 (Site d))} (h : ω₁ ≤ ω₂) :
    openSubgraph d ω₁ ≤ openSubgraph d ω₂ := by
  intro x y hxy
  rw [openSubgraph_adj] at hxy ⊢
  refine ⟨hxy.1, ?_⟩
  have hle := h s(x, y); rw [hxy.2] at hle
  exact le_antisymm (Bool.le_true _) hle


theorem connected_mono {ω₁ ω₂ : ConfigSpace (Sym2 (Site d))} (h : ω₁ ≤ ω₂)
    {x y : Site d} (hc : Connected d ω₁ x y) : Connected d ω₂ x y :=
  hc.mono (openSubgraph_mono h)


theorem connectedToSet_mono {edge : E → Sym2 (Site d)} {o : Site d} {B : Set (Site d)}
    {ω₁ ω₂ : ConfigSpace E} (h : ω₁ ≤ ω₂)
    (hc : ConnectedToSet d (liftCfg edge ω₁) o B) :
    ConnectedToSet d (liftCfg edge ω₂) o B := by
  obtain ⟨b, hbB, hconn⟩ := hc
  exact ⟨b, hbB, connected_mono (liftCfg_monotone edge h) hconn⟩


theorem connectedToSet_increasing (edge : E → Sym2 (Site d)) (o : Site d) (B : Set (Site d)) :
    IsIncreasing {ω : ConfigSpace E | ConnectedToSet d (liftCfg edge ω) o B} := by
  intro ω₁ ω₂ h hmem
  exact connectedToSet_mono h hmem


end Lattice
end OSSS
end StatMech
