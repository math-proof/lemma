/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/FieldExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace FieldExtensions

noncomputable example (K : Type*) [Field K] (p : Polynomial K) :
    Field p.SplittingField := Polynomial.SplittingField.instField p

end FieldExtensions
