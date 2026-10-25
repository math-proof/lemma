/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDimensionCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.ChevalleyImage
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ChevalleyImage
import Structure.v1.Atlas.AlgebraicGeometryI.code.BertiniDimensionCount


namespace BertiniArithmetic

/-- Opaque predicate: a hyperplane gives a smooth section of `X`. -/
opaque SmoothSubvariety.isSmoothSection (X : SmoothSubvariety) :
    X.HyperplaneIndex → Prop

end BertiniArithmetic
