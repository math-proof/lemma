/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
open scoped BigOperators
open Matrix Module

set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def kerLap (ω : ConfigSpace (Sym2 V)) : Submodule ℝ (V → ℝ) :=
  LinearMap.ker (Matrix.toLin' ((openSub G ω).lapMatrix ℝ))


end FK
end StatMech
