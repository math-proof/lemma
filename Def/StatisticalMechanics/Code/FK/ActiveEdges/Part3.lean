module
public import Theorem.StatisticalMechanics.Code.FK.InhomogeneousFKG
public import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
public import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
public import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part2
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


section Fiber

variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def openMarginal (μ : ConfigSpace E → ℝ) (e : E) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace E => ω e = true), μ ω

end Fiber
end FK
end StatMech
