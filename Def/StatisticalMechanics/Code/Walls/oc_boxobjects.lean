/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
import Theorem.StatisticalMechanics.Code.FK.FKQ2Sharp
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
open scoped BigOperators
open Finset Set
open scoped Classical

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace Walls

open StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def oc_theta (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]
    (Af : ℕ → Set (ConfigSpace (Sym2 V))) (n : ℕ) (β : ℝ) : ℝ :=
  fkProbOf (Gf n) β 2 (Af n)


noncomputable def oc_S (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]
    (Af : ℕ → Set (ConfigSpace (Sym2 V))) (n : ℕ) (β : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, oc_theta Gf Af k β

end Walls
end StatMech
