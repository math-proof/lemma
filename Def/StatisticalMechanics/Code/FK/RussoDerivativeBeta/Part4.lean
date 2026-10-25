/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBeta.Part3
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def fkProbWOf (pf : Sym2 V → ℝ) (q : ℝ)
    (A : Set (ConfigSpace (Sym2 V))) : ℝ :=
  fkMeanW G pf q (A.indicator (fun _ => (1 : ℝ)))


end FK
end StatMech
