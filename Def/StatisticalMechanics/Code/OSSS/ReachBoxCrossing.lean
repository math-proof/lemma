/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.RevealmentBoxCrossing.Part3
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part7
import Theorem.StatisticalMechanics.Code.OSSS.ReachBoxCrossing
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace ReachBoxCrossing

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability

open StatMech.OSSS.MonotonicFK

open StatMech.OSSS.AdaptDisintegration

open OSSS.GrandCoupling OSSS.Coding

open StatMech.OSSS.RevealmentBoundAssembly

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.RevealmentConstruction

open StatMech.Lattice

variable {E : Type*} [Fintype E] [DecidableEq E]


variable {V : Type*} [DecidableEq V]


def FrontierConn {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (endU endV : E → V)
    (B : Set V) (e : E) : Prop :=
  ∀ X : ConfigSpace E, ¬ detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) →
    ConnOpenSet endU endV X (endU e) B ∨ ConnOpenSet endU endV X (endV e) B


end ReachBoxCrossing
end OSSS
end StatMech
