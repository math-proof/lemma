/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part4


namespace StatMech.Universality

open Complex


noncomputable def isingContour (F : ℂ → ℂ) (z : Fin 4 → ℂ) : ℂ :=
  ∑ i : Fin 4, F ((z i + z (i + 1)) / 2) * (z (i + 1) - z i)


end StatMech.Universality
