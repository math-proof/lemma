/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part3
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


theorem streamPotential_vertical_boundary
    (C : IntegralSquareTorusCycle L) (p : ZMod L × ZMod L) :
    C.streamPotential (p.1 - 1, p.2) - C.streamPotential p =
      C.zeroFluxVertical p := by
  have hv := zmodPrefix_sub_pred_of_sum_zero
    (fun x => C.zeroFluxVertical (x, p.2))
    (C.zeroFluxVertical_sum_zero p.2) p.1
  unfold streamPotential
  linarith

theorem streamPotential_horizontal_boundary
    (C : IntegralSquareTorusCycle L) (p : ZMod L × ZMod L) :
    C.streamPotential p - C.streamPotential (p.1, p.2 - 1) =
      C.zeroFluxHorizontal p := by
  have hh := zmodPrefix_sub_pred_of_sum_zero
    (fun y => C.zeroFluxHorizontal (0, y))
    (C.zeroFluxHorizontal_sum_zero 0) p.2
  have hprefixDiff :
      ons_zmodPrefix (fun x => C.zeroFluxVertical (x, p.2)) p.1 -
        ons_zmodPrefix (fun x => C.zeroFluxVertical (x, p.2 - 1)) p.1 =
      C.zeroFluxHorizontal (0, p.2) -
        C.zeroFluxHorizontal (p.1, p.2) := by
    unfold ons_zmodPrefix
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ i ∈ Finset.range p.1.val,
          (C.zeroFluxVertical (((i + 1 : Nat) : ZMod L), p.2) -
            C.zeroFluxVertical (((i + 1 : Nat) : ZMod L), p.2 - 1))) =
          ∑ i ∈ Finset.range p.1.val,
            (C.zeroFluxHorizontal (((i : Nat) : ZMod L), p.2) -
              C.zeroFluxHorizontal (((i + 1 : Nat) : ZMod L), p.2)) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hdiv := C.zeroFlux_divergence_zero
              (((i + 1 : Nat) : ZMod L), p.2)
            have hsub : (((i + 1 : Nat) : ZMod L) - 1) =
                (i : ZMod L) := by
              rw [Nat.cast_add, Nat.cast_one]
              ring
            rw [hsub] at hdiv
            linarith
      _ = C.zeroFluxHorizontal (0, p.2) -
          C.zeroFluxHorizontal (((p.1.val : Nat) : ZMod L), p.2) := by
            rw [Finset.sum_range_sub']
            simp only [Nat.cast_zero]
      _ = C.zeroFluxHorizontal (0, p.2) -
          C.zeroFluxHorizontal (p.1, p.2) := by
            rw [ZMod.natCast_zmod_val]
  change
    (ons_zmodPrefix (fun y => C.zeroFluxHorizontal (0, y)) p.2 -
        ons_zmodPrefix (fun x => C.zeroFluxVertical (x, p.2)) p.1) -
      (ons_zmodPrefix (fun y => C.zeroFluxHorizontal (0, y)) (p.2 - 1) -
        ons_zmodPrefix (fun x => C.zeroFluxVertical (x, p.2 - 1)) p.1) =
      C.zeroFluxHorizontal p
  linarith


end IntegralSquareTorusCycle
end
end StatMech.FrontierD
