/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace StatMech.Universality

open Complex


noncomputable def isingLambda : ℂ := Complex.exp ((Real.pi / 4 : ℝ) * Complex.I)


end StatMech.Universality
