/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/SpaceFillingCurve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


noncomputable section

open Finset NNReal ENNReal

namespace SpaceFillingCurve

/-- The unit square $[0,1]^2 \subseteq \mathbb{R}^2$. -/
def unitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∀ j : Fin 2, p j ∈ Set.Icc (0 : ℝ) 1}

/-- Cyclic successor on `Fin n`: $i \mapsto (i + 1) \bmod n$. -/
def cyclicSucc {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩

end SpaceFillingCurve
end
