/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeighted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLoops
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
import Def.StatisticalMechanics.Code.Onsager.KWWeighted.Part2


namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_KWmatWeightedPhase_const (L : ℕ) (x omega u v : ℂ) :
    ons_KWmatWeightedPhase L (fun _ => x) omega u v =
      ons_KWmatPhase L x omega u v := by
  ext d2 d1
  simp only [ons_KWmatWeightedPhase, ons_KWmatWeighted_const,
    ons_KWmatPhase]

theorem ons_loopWeight_KWmatWeightedPhase
    {L n : ℕ} [NeZero L] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega u v : ℂ)
    (d : Fin n → ons_Dart L) :
    ons_loopWeight (ons_KWmatWeightedPhase L weight omega u v) d =
      (∏ k, ons_dirPhase u v (d k).2) *
        ons_loopWeight (ons_KWmatWeighted L weight omega) d := by
  unfold ons_loopWeight ons_KWmatWeightedPhase
  rw [Finset.prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp (Equiv.addRight (1 : Fin n))
    (fun k => ons_dirPhase u v (d k).2)

end StatMech.Onsager
