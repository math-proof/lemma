/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBeta
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def edgeProductWOff (pf : Sym2 V → ℝ) (e₀ : Sym2 V)
    (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∏ j ∈ G.edgeFinset.erase e₀, (if ω j then pf j else 1 - pf j)


end FK
end StatMech
