/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.CardyDiscreteHolo.Part3


namespace StatMech.Universality

open Complex


noncomputable def triContour (F : ℂ → ℂ) (z : Fin 3 → ℂ) : ℂ :=
  ∑ i : Fin 3, F ((z i + z (i + 1)) / 2) * (z (i + 1) - z i)


end StatMech.Universality
