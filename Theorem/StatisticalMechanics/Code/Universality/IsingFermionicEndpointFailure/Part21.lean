/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part23


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem mirrorOnlyOrderedHorizontalCover_value
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R) (hhalf : R <= 2 * level)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q)
    (w : IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)) :
    orderedFarHorizontalEndpointValue (R - level) R t
        ⟨2 * level - R, by omega⟩ q.1 (p.2.1 : Int) (q.2.1 : Int)
        (mirrorOnlyOrderedHorizontalCover R level t p p' q
          hlevelR hhalf hstart hmirror hq w) = w.1 := by
  exact Classical.choose_spec ((Classical.choose_spec
    (exists_mirrorOnlyOrderedCover R level t p p' q
      hlevelR hstart hmirror hq w)).2 hhalf)

theorem mirrorOnlyOrderedHorizontalCover_injective
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R) (hhalf : R <= 2 * level)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q) :
    Function.Injective (mirrorOnlyOrderedHorizontalCover R level t p p' q
      hlevelR hhalf hstart hmirror hq) := by
  intro a b hab
  apply Subtype.ext
  rw [← mirrorOnlyOrderedHorizontalCover_value R level t p p' q
      hlevelR hhalf hstart hmirror hq a,
    ← mirrorOnlyOrderedHorizontalCover_value R level t p p' q
      hlevelR hhalf hstart hmirror hq b, hab]

theorem natCard_mirrorOnlySourceOutputAt_le_orderedFarHorizontalEndpoint
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R) (hhalf : R <= 2 * level)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R t p p' q (level : Int)) <=
      Nat.card (IsingOrderedFarHorizontalEndpointFamily (R - level) R t
        ⟨2 * level - R, by omega⟩ q.1 (p.2.1 : Int) (q.2.1 : Int)) :=
  Nat.card_le_card_of_injective
    (mirrorOnlyOrderedHorizontalCover R level t p p' q
      hlevelR hhalf hstart hmirror hq)
    (mirrorOnlyOrderedHorizontalCover_injective R level t p p' q
      hlevelR hhalf hstart hmirror hq)

theorem mirrorOnlySourceOutputAt_horizontal_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hright : level + rho <= R)
    (hhalf : R <= 2 * level)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  have hlevelR : level <= R := by omega
  have hq : isingLeapfrogBoxBoundary R q := by
    unfold isingLeapfrogBoxBoundary
    rcases hqHorizontal with hq | hq
    · left; exact hq
    · right; left; omega
  have hcard :=
    natCard_mirrorOnlySourceOutputAt_le_orderedFarHorizontalEndpoint
      R level (rho * rho) p p' q hlevelR hhalf hstart hmirror hq
  have hm : 0 < R - level := by omega
  have hρm : rho <= R - level := by omega
  have ht : rho * rho <= (R - level) * (R - level) :=
    Nat.mul_self_le_mul_self hρm
  have hordered := orderedFarHorizontalEndpoint_weight_le
    (R - level) R (rho * rho) ⟨2 * level - R, by omega⟩ q.1
      (p.2.1 : Int) (q.2.1 : Int) hm ht (by
        unfold isingLineBoxBoundary
        exact hqHorizontal)
  have hsq : (rho : Real) ^ 2 <= ((R - level : Nat) : Real) ^ 2 := by
    exact_mod_cast (show rho ^ 2 <= (R - level) ^ 2 by
      simpa [pow_two] using ht)
  calc
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      Nat.card (IsingOrderedFarHorizontalEndpointFamily (R - level) R
        (rho * rho) ⟨2 * level - R, by omega⟩ q.1
        (p.2.1 : Int) (q.2.1 : Int)) /
        (4 : Real) ^ (rho * rho) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ <= 468 / ((R - level : Nat) : Real) ^ 2 := hordered
    _ <= 468 / (rho : Real) ^ 2 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq

theorem mirrorOnlySourceOutputAt_boundary_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hright : level + rho <= R)
    (hhalf : R <= 2 * level)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      7488 / (rho : Real) ^ 2 := by
  unfold isingLeapfrogBoxBoundary at hqBoundary
  rcases hqBoundary with hqLeft | hqRight | hqBottom | hqTop
  · exact (mirrorOnlySourceOutputAt_horizontal_diffusive_weight_le
      R level rho p p' q hstart hmirror hρ hright hhalf (Or.inl hqLeft)).trans
        (by
          apply div_le_div_of_nonneg_right (by norm_num)
          positivity)
  · exact (mirrorOnlySourceOutputAt_horizontal_diffusive_weight_le
      R level rho p p' q hstart hmirror hρ hright hhalf
        (Or.inr (by omega))).trans (by
          apply div_le_div_of_nonneg_right (by norm_num)
          positivity)
  · exact mirrorOnlySourceOutputAt_vertical_diffusive_weight_le
      R level rho p p' q hstart hmirror hρ hright (Or.inl hqBottom)
  · exact mirrorOnlySourceOutputAt_vertical_diffusive_weight_le
      R level rho p p' q hstart hmirror hρ hright (Or.inr (by omega))

theorem mirrorFailureAt_boundary_diffusive_weight_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R) (hhalf : R <= 2 * level)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hbottom' : rho <= p'.2.1) (htop' : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      8424 / (rho : Real) ^ 2 := by
  have hcard := natCard_mirrorFailureAt_le_aligned_add_residual
    R (rho * rho) p p' q (level : Int)
  have hcardReal :
      (Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
        R (rho * rho) p p' q (level : Int)) : Real) <=
      Nat.card (IsingSourceFailureOutputAtFamily
        R (rho * rho) p q (level : Int)) +
      Nat.card (IsingMirrorFailureOutputAtFamily
        R (rho * rho) p p' q (level : Int)) +
      Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R (rho * rho) p p' q (level : Int)) := by
    exact_mod_cast hcard
  have hsource := sourceFailureOutputAt_boundary_diffusive_weight_le
    R level rho p q hstart hρ hleft (by omega) hbottom htop hqBoundary
  have hmirrorBound := mirrorFailureOutputAt_boundary_diffusive_weight_le
    R level rho p p' q hstart hmirror hρ (lt_of_lt_of_le hρ hleft)
      hright hbottom' htop' hqBoundary
  have hresidual := mirrorOnlySourceOutputAt_boundary_diffusive_weight_le
    R level rho p p' q hstart hmirror hρ hright hhalf hqBoundary
  calc
    Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      (Nat.card (IsingSourceFailureOutputAtFamily
          R (rho * rho) p q (level : Int)) +
       Nat.card (IsingMirrorFailureOutputAtFamily
          R (rho * rho) p p' q (level : Int)) +
       Nat.card (IsingMirrorOnlySourceOutputAtFamily
          R (rho * rho) p p' q (level : Int))) /
        (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = Nat.card (IsingSourceFailureOutputAtFamily
          R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorFailureOutputAtFamily
          R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorOnlySourceOutputAtFamily
          R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) := by
      ring
    _ <= 468 / (rho : Real) ^ 2 + 468 / (rho : Real) ^ 2 +
        7488 / (rho : Real) ^ 2 := add_le_add (add_le_add hsource hmirrorBound)
      hresidual
    _ = 8424 / (rho : Real) ^ 2 := by ring

end
end StatMech.Universality
