module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
public import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
public import Theorem.StatisticalMechanics.Code.Inequalities.FKG
public import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part3
open scoped BigOperators symmDiff
open Finset SimpleGraph Set
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ghsLTWeight (β h : ℝ) (q a : ConfigSpace V) : ℝ :=
  Real.exp (2 * β *
    ((∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e)
      + h * ∑ v ∈ ghsLAgreeFinset q, spin a v))


noncomputable def ghsLUWeight (β : ℝ) (q a : ConfigSpace V) : ℝ :=
  Real.exp (2 * β *
    ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ, bond a e)


end Ising
end StatMech
