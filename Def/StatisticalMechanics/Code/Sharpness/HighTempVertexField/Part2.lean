/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempVertexField
open Finset SimpleGraph
open scoped BigOperators Classical

set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

open Ising

open FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def vertexFieldWeight (β : ℝ) (J : Sym2 V → ℝ)
    (H : V → ℝ) (s : ConfigSpace V) : ℝ :=
  Real.exp (β * ((∑ e ∈ G.edgeFinset, J e * bond s e) +
    ∑ x : V, H x * spin s x))


noncomputable def vertexFieldZ (β : ℝ) (J : Sym2 V → ℝ)
    (H : V → ℝ) : ℝ :=
  ∑ s : ConfigSpace V, vertexFieldWeight G β J H s


noncomputable def vertexFieldExpectation (β : ℝ) (J : Sym2 V → ℝ)
    (H : V → ℝ) (f : ConfigSpace V → ℝ) : ℝ :=
  (∑ s : ConfigSpace V, f s * vertexFieldWeight G β J H s) /
    vertexFieldZ G β J H


noncomputable def vertexFieldTwoPoint (β : ℝ) (J : Sym2 V → ℝ)
    (H : V → ℝ) (a b : V) : ℝ :=
  vertexFieldExpectation G β J H (spinProd (sourcePair a b))


end Sharpness
end StatMech
