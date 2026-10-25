/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.IsingSHolo.Part6


namespace StatMech.Universality

open Complex


theorem isingFace_midpoints (v d : ℂ) :
    ((isingFace v d 0 + isingFace v d 1) / 2 = v + (1 + Complex.I) / 2 * d) ∧
    ((isingFace v d 1 + isingFace v d 2) / 2 = v + (-1 + Complex.I) / 2 * d) ∧
    ((isingFace v d 2 + isingFace v d 3) / 2 = v + (-1 - Complex.I) / 2 * d) ∧
    ((isingFace v d 3 + isingFace v d 0) / 2 = v + (1 - Complex.I) / 2 * d) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [isingFace, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] <;> ring


theorem isingFace_edges (v d : ℂ) :
    (isingFace v d 1 - isingFace v d 0 = (Complex.I - 1) * d) ∧
    (isingFace v d 2 - isingFace v d 1 = (-1 - Complex.I) * d) ∧
    (isingFace v d 3 - isingFace v d 2 = (1 - Complex.I) * d) ∧
    (isingFace v d 0 - isingFace v d 3 = (1 + Complex.I) * d) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [isingFace, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] <;> ring


end StatMech.Universality
