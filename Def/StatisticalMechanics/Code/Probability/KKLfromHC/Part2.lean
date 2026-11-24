module
public import Theorem.StatisticalMechanics.Code.Probability.VectorTwoPoint
public import Theorem.StatisticalMechanics.Code.Probability.KKLInequality.Part4
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Theorem.StatisticalMechanics.Code.Probability.KKLfromHC
open scoped BigOperators
open Finset
set_option linter.style.longLine false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


noncomputable def khc_walshChar (S : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ i ∈ S, khc_sign (x i)

end Probability
end StatMech
