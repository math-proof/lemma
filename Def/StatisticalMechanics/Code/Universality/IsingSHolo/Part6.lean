/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part5


namespace StatMech.Universality

open Complex


noncomputable def isingFace (v d : ℂ) : Fin 4 → ℂ :=
  ![v + d, v + Complex.I * d, v - d, v - Complex.I * d]


end StatMech.Universality
