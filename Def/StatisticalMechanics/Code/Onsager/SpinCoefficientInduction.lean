/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.SpinWeightedBase


namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

def ons_restrictEdgeWeight
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (S : Finset (Sym2 (ZMod L × ZMod L))) :
    Sym2 (ZMod L × ZMod L) → ℂ :=
  fun edge => if edge ∈ S then weight edge else 0

end StatMech.Onsager
