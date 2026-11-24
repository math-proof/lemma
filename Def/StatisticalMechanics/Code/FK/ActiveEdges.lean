module
public import Theorem.StatisticalMechanics.Code.FK.InhomogeneousFKG
public import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
public import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
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


noncomputable def extendActive (ω : ConfigSpace G.edgeSet) : ConfigSpace (Sym2 V) :=
  fun e => if h : e ∈ G.edgeSet then ω ⟨e, h⟩ else false

end FK
end StatMech
