/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.Green25_upper_solution.Part5
open Asymptotics Filter Finset


namespace Green25

lemma shift25_injective (a : ℕ) : Function.Injective (shift25 a) := by
  intro s t h
  ext x
  have hmem := Finset.ext_iff.mp h (a + x)
  simpa [shift25] using hmem

end Green25
