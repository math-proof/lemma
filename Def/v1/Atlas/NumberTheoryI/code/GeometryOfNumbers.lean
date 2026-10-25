/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GeometryOfNumbers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.DirichletSeries.Part4
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.DirichletSeries
import Abbrev.v1.Atlas.NumberTheoryI.code.GeometryOfNumbers
universe u


noncomputable section

open MeasureTheory Measure Set Submodule ZLattice Module

open scoped NumberField

namespace GeometryOfNumbers

def IsSymmetricSet {V : Type*} [AddCommGroup V] (S : Set V) : Prop :=
  -S = S


end GeometryOfNumbers
end
