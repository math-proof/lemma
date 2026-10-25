/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Ising.Pressure.Part3
open scoped BigOperators
open Finset Filter Topology


namespace StatMech

namespace Ising

noncomputable def pressure {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) : ℝ :=
  (logZSeq_subadditive β E).lim


end Ising
end StatMech
