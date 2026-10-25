/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Def.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part3
open MeasureTheory Finset
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {E : Type*}


theorem downCompress_card [Fintype E] [DecidableEq E] (i : E) (𝒜 : Finset (ConfigSpace E)) :
    (downCompress i 𝒜).card = 𝒜.card := by
  unfold downCompress
  rw [Finset.card_image_of_injOn, Down.card_compression, Finset.card_image_of_injOn]
  · intro x _ y _ h
    have := congrArg supportCfg h
    rwa [supportCfg_cfgSupport, supportCfg_cfgSupport] at this
  · intro x _ y _ h
    have := congrArg cfgSupport h
    rwa [cfgSupport_supportCfg, cfgSupport_supportCfg] at this


lemma mem_downCompress [Fintype E] [DecidableEq E] (i : E) (𝒜 : Finset (ConfigSpace E))
    (ω : ConfigSpace E) :
    ω ∈ downCompress i 𝒜 ↔ cfgSupport ω ∈ Down.compression i (𝒜.image cfgSupport) := by
  unfold downCompress
  rw [Finset.mem_image]
  refine ⟨?_, fun h => ⟨cfgSupport ω, h, supportCfg_cfgSupport ω⟩⟩
  rintro ⟨s, hs, rfl⟩
  rwa [cfgSupport_supportCfg]


end StatMech
