/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeABridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Matrix
import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeACoxeterSystem.Part2
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper


namespace TypeABridge

/-- The explicit numeric matrix for the type-$A$ Coxeter system on $\operatorname{Fin}(n)$. -/
def glnCoxeterMatrixA (n : ℕ) : Matrix (Fin n) (Fin n) ℕ := fun i j =>
  if i = j then 1
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 3
  else 2

end TypeABridge
