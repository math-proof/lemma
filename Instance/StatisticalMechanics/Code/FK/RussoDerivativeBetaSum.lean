/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBeta.Part4
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]


instance canonicalSym2Fintype : Fintype (Sym2 V) := Sym2.instFintype

instance canonicalEdgeFintype (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype G.edgeSet :=
  @SimpleGraph.fintypeEdgeSet V G Sym2.instFintype inferInstance

end FK
end StatMech
