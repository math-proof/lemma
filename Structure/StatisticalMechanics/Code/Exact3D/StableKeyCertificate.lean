/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39


public section

namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

structure StableKeyRecord where
  support : List (List ℤ)
  degree : ℕ
  range : ℕ
deriving DecidableEq, Repr

end BoundedPolymerCase
end Exact3D
end StatMech
