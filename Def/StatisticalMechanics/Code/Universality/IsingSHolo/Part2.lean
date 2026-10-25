/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo


namespace StatMech.Universality

open Complex


noncomputable def isingProj (e x : ℂ) : ℂ :=
  (1 / 2) * (x + (starRingEnd ℂ) e * (starRingEnd ℂ) x)


end StatMech.Universality
