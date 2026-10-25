/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBetaSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBeta.Part4
import Instance.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def betaParams (J : Sym2 V → ℝ) (β : ℝ) : Sym2 V → ℝ :=
  fun e => 1 - Real.exp (-(β * J e))

noncomputable def betaScore (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V → ℝ) (β : ℝ)
    (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∑ e ∈ G.edgeFinset,
    (J e / betaParams J β e) * (coordR e ω - betaParams J β e)

end FK
end StatMech
