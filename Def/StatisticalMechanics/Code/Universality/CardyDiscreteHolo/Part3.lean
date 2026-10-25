/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.Universality.CardyDiscreteHolo


namespace StatMech.Universality

open Complex


namespace CardyLocalConfig

attribute [instance] CardyLocalConfig.fin

variable (L : CardyLocalConfig)


noncomputable def crossingFun (x : ZMod 3) : ℂ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => L.arc ω = x), L.weight ω


noncomputable def cardyS : ℂ := ∑ ω, cardyWpow (L.arc ω) * L.weight ω


end CardyLocalConfig
end StatMech.Universality
