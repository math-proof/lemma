module
public import Theorem.StatisticalMechanics.Code.FK.InhomogeneousFKG
public import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
public import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
public import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part3
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


section ClosedProduct

variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def closedProd (S : Finset E) (ω : ConfigSpace E) : ℝ :=
  ∏ e ∈ S, if ω e then 0 else 1

end ClosedProduct
end FK
end StatMech
