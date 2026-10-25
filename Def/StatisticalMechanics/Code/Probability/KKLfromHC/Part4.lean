/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.VectorTwoPoint
import Theorem.StatisticalMechanics.Code.Probability.KKLInequality.Part4
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Theorem.StatisticalMechanics.Code.Probability.KKLfromHC.Part3
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


noncomputable def khc_reindex {κ : Type*} (e : κ ≃ ι) (f : (ι → Bool) → ℝ) :
    (κ → Bool) → ℝ :=
  fun y => f (fun i => y (e.symm i))


def khc_cubeEquiv {κ : Type*} (e : κ ≃ ι) : (ι → Bool) ≃ (κ → Bool) :=
  Equiv.arrowCongr e.symm (Equiv.refl Bool)


end Probability
end StatMech
