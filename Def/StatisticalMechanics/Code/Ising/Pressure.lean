/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
open scoped BigOperators
open Finset Filter Topology


namespace StatMech

namespace Ising

noncomputable def Z {Ω : Type*} [Fintype Ω] (β : ℝ) (E : Ω → ℝ) : ℝ :=
  ∑ s : Ω, Real.exp (-β * E s)


end Ising
end StatMech
