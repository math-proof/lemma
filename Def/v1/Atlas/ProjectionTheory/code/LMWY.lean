/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LMWY.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Matrix


namespace HomogeneousDynamics

/-- The arithmetic lattice $SL(3, \mathbb{Z})$ viewed as a subgroup of $SL(3, \mathbb{R})$
via the canonical embedding. -/
noncomputable def SL3Z : Subgroup (SpecialLinearGroup (Fin 3) ℝ) :=
  (SpecialLinearGroup.map (Int.castRingHom ℝ)).range

/-- The unipotent matrix $U(t) = \begin{pmatrix} 1 & t & t^2 \\ 0 & 1 & t \\ 0 & 0 & 1 \end{pmatrix}$
parameterizing the one-parameter unipotent subgroup of $SL(3, \mathbb{R})$ used in
Lindenstrauss–Mohammadi–Wang–Yang. -/
noncomputable def unipotentU (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, t, t^2; 0, 1, t; 0, 0, 1]

end HomogeneousDynamics
