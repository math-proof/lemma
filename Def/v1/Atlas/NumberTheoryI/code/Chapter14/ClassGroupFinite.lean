module
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Def.v1.Atlas.NumberTheoryI.code.GeometryOfNumbers.Part2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.GeometryOfNumbers
open NumberField


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter14/ClassGroupFinite.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace ClassGroupFinite

noncomputable def minkowskiConstant (K : Type*) [Field K] [NumberField K] : ℝ :=
  (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
  ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K) ^ Module.finrank ℚ K *
   √|↑(discr K)|)

end ClassGroupFinite
