/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.PrefixCoversClose.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKRevealmentClose
import Theorem.StatisticalMechanics.Code.OSSS.PerScaleRevealmentClose
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace PerScaleRevealmentClose

open OSSS.Coding

open OSSS.AdaptMConditional

open StatMech.OSSS

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.ReachDomination

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.PrefixCoversClose

open StatMech.OSSS.FKRevealmentClose

open StatMech.OSSS.MonotonicFK

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


def psr_FamilyFrontierConn {κ : Type*} {nE : ℕ} (σf : κ → (Fin nE ≃ E))
    (f : ConfigSpace E → ℝ) (endU endV : E → V) (B : κ → Set V) : Prop :=
  ∀ (k : κ) (e : E), FrontierConn (σf k) f endU endV (B k) e

end PerScaleRevealmentClose
end OSSS
end StatMech
