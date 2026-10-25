/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeighted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLoops
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
import Def.StatisticalMechanics.Code.Onsager.KWWeighted


namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_KWmatWeighted_const (L : ℕ) (x omega : ℂ) :
    ons_KWmatWeighted L (fun _ => x) omega = ons_KWmat L x omega := by
  ext d2 d1
  simp only [ons_KWmatWeighted, ons_KWmat]

theorem ons_loopWeight_KWmatWeighted_eq
    {L n : ℕ} [NeZero L] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega : ℂ)
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_loopWeight (ons_KWmatWeighted L weight omega) d =
      (∏ k, weight (ons_portEdge L (d k))) *
        ∏ k, ons_turnW omega (d (k + 1)).2 (d k).2 := by
  unfold ons_loopWeight ons_KWmatWeighted
  have hfac : ∀ k : Fin n,
      (if (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1 then
          weight (ons_portEdge L (d (k + 1))) *
            ons_turnW omega (d (k + 1)).2 (d k).2
        else 0) =
      weight (ons_portEdge L (d (k + 1))) *
        ons_turnW omega (d (k + 1)).2 (d k).2 := by
    intro k
    rw [if_pos (hvalid k)]
  rw [Finset.prod_congr rfl (fun k _ => hfac k),
    Finset.prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp (Equiv.addRight (1 : Fin n))
    (fun k => weight (ons_portEdge L (d k)))

end StatMech.Onsager
