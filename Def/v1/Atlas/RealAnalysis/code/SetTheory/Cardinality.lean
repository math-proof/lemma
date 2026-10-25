/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/SetTheory/Cardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace SetTheory.Cardinality

/-- `SameCardinality A B` states that `A` and `B` have the same cardinality, i.e. there exists
a bijection between them (`A ≃ B`). -/
def SameCardinality (A B : Type*) : Prop := Nonempty (A ≃ B)

end SetTheory.Cardinality
