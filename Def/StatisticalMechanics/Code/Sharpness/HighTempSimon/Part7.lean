/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part4
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def highTempSwitchInputWeight (t : Sym2 V → ℝ)
    (p : HighTempSwitchInput (V := V)) : ℝ :=
  (∏ e ∈ p.F, t e) * ∏ e ∈ p.H, t e

noncomputable def highTempSwitchOutputWeight (t : Sym2 V → ℝ)
    (r : HighTempSwitchOutput (V := V)) : ℝ :=
  (∏ e ∈ r.A, t e) * t s(r.x, r.y) * ∏ e ∈ r.B, t e


end Sharpness
end StatMech
