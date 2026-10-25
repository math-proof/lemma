/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace AdaptMConditional

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.LindebergTree OSSS.AdaptiveTau

variable {E : Type*} [Fintype E] [DecidableEq E]


def mixUV {n : ℕ} (U V : Fin n → ℝ) (m : ℕ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < m then U i else V i


def adaptWt {n : ℕ} (U V : Fin n → ℝ) (m t : ℕ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < t then V i else if (i : ℕ) < m then U i else V i


end AdaptMConditional
end OSSS
end StatMech
