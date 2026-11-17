/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
public import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue

noncomputable section

open scoped NumberField

namespace RayClassField

public inductive Place (K : Type*) [Field K] [NumberField K] where
  | finite : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → Place K
  | infinite : NumberField.InfinitePlace K → Place K

end RayClassField
end
