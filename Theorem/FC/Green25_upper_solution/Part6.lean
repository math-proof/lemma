module
public import Mathlib
public import Def.FC.Green25_upper_solution.Part6
open Asymptotics Filter Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace Green25

lemma shiftPartition25_card {s : Finset ℕ} (a : ℕ) (P : Finpartition s) :
    #(shiftPartition25 a P).parts = #P.parts := by
  exact Finset.card_image_iff.mpr fun _ _ _ _ h => shift25_injective a h

end Green25
