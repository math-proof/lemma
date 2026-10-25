/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.CardyDiscreteHolo


namespace StatMech.Universality

open Complex


noncomputable def cardyWpow (k : ZMod 3) : ℂ := cardyOmega ^ (k.val)

end StatMech.Universality
