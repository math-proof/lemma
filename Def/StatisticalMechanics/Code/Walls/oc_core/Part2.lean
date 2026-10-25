/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part7
import Theorem.StatisticalMechanics.Code.OSSS.SharpnessFK
import Theorem.StatisticalMechanics.Code.Walls.oc_boxcrossingscalesum
import Theorem.StatisticalMechanics.Code.Walls.oc_boxobjects.Part2
import Abbrev.StatisticalMechanics.Code.Walls.oc_core
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]


section Headline

variable {d : ℕ}


noncomputable def oc_Rscale {ν : E → Bool → ℝ} (edge : E → Sym2 (Site d))
    (endU endV : E → Site d) (n : ℕ) (k : oc_ScaleIdx n) (e : E) : ℝ :=
  (expect ν fun ω =>
      if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k.1) then (1 : ℝ) else 0)
    + (expect ν fun ω =>
        if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k.1) then (1 : ℝ) else 0)


end Headline
end Walls
end StatMech
