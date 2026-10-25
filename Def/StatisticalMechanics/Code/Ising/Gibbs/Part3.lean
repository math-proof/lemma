/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part2
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def hamiltonian (h : ℝ) (s : ConfigSpace V) : ℝ :=
  - (∑ e ∈ G.edgeFinset, bond s e) - h * ∑ x, spin s x


noncomputable def isingWeight (β h : ℝ) (s : ConfigSpace V) : ℝ :=
  Real.exp (-β * hamiltonian G h s)

end Ising
end StatMech
