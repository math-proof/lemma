/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Theorem.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov.Part3
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def edgeSubsetExteriorEdgeFactor
    (K H : SimpleGraph V) [DecidableRel K.Adj] [DecidableRel H.Adj]
    (psi : ConfigSpace (Sym2 V)) (p : Real) : Real :=
  ∏ e ∈ H.edgeFinset \ K.edgeFinset, if psi e then p else 1 - p

end
end StatMech.FK
