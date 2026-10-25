/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.IsingSHolo.Part2


namespace StatMech.Universality

open Complex


theorem isingProj_add (e x y : ℂ) :
    isingProj e (x + y) = isingProj e x + isingProj e y := by
  unfold isingProj
  rw [map_add]; ring


theorem isingProj_of_arg (e Fe : ℂ) (he : Complex.normSq e = 1)
    (harg : (starRingEnd ℂ) Fe = e * Fe) : isingProj e Fe = Fe := by
  unfold isingProj
  rw [harg, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self, he]
  push_cast; ring


end StatMech.Universality
