module
public import Mathlib
public import Def.v1.Atlas.NumberTheoryI.code.DirichletSeries.Part4
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.DirichletSeries
public import Abbrev.v1.Atlas.NumberTheoryI.code.GeometryOfNumbers.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GeometryOfNumbers.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u


noncomputable section

open MeasureTheory Measure Set Submodule ZLattice Module

open scoped NumberField

namespace GeometryOfNumbers

open NumberField.InfinitePlace NumberField.mixedEmbedding in
alias convex_body_volume := convexBodySum_volume

open NumberField in

def IsUnramifiedOutside (K : Type*) [Field K] [NumberField K] (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S → ¬((p : ℤ) ∣ discr K)

end GeometryOfNumbers
end
