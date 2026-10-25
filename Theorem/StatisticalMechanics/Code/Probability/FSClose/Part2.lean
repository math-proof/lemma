/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.EntropySubadditivity.Part2
import Theorem.StatisticalMechanics.Code.Probability.GlobalLSI
import Def.StatisticalMechanics.Code.Probability.FSClose
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS


variable {E : Type*} [Fintype E] [DecidableEq E]

theorem fsc2_entMassFamily_holds {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] (φ : ConfigSpace E → Bool) :
    fsc2_EntMassFamily p φ :=
  fun ρ _ _ => fsc2_lsi_spectral_noiseOp hp0 hp1 ρ (fun ω => if φ ω then (1 : ℝ) else 0)


end StatMech.Probability
