/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Definitions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Finprod
public import Abbrev.v1.Atlas.BooleanFunctions.code.Definitions

@[expose] public section

namespace BooleanFourier

open Finset in
noncomputable def lpNorm (p : ℝ) (f : BoolFn n) : ℝ :=
  ((1 / (2 ^ n : ℝ)) * ∑ x : Fin n → Bool, |f x| ^ p) ^ (1 / p)

end BooleanFourier
