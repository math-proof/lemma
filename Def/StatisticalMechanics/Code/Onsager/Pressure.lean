/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Pressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.HighTemp
import Theorem.StatisticalMechanics.Code.Onsager.Pressure
open scoped BigOperators
open Finset


namespace StatMech

namespace Onsager

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ons_pressureFinite (β : ℝ) : ℝ :=
  Real.log (ons_Z G β) / (Fintype.card V : ℝ)


end Onsager
end StatMech
