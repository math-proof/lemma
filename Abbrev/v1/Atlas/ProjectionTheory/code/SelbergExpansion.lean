/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Matrix Finset BigOperators


noncomputable section

namespace SelbergExpansion

/-- The group `SL₂(𝔽_p)` of `2 × 2` matrices of determinant `1` over `ℤ/pℤ`. -/
abbrev SL2 (p : ℕ) := SpecialLinearGroup (Fin 2) (ZMod p)

end SelbergExpansion
end
