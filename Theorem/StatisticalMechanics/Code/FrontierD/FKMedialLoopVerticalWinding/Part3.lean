/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}


theorem fkOrientedMedialLoopVerticalFlux_downwardMode
    (pairing : FKMedialLoopPairing T) (C : FKMedialLoop T pairing) :
    fkOrientedMedialLoopVerticalFlux pairing
        (FKMedialTurningFiber.arrowsOfMode pairing
          (fkMedialDownwardVerticalMode pairing)) C =
      -((fkMedialLoopCanonicalVerticalFlux pairing C).natAbs : Int) := by
  rw [fkOrientedMedialLoopVerticalFlux_arrowsOfMode]
  unfold fkMedialDownwardVerticalMode
  by_cases h : 0 ≤ fkMedialLoopCanonicalVerticalFlux pairing C
  · simp [h, Int.natAbs_of_nonneg h]
  · rw [if_neg (by simpa using h)]
    rcases Int.natAbs_eq
        (fkMedialLoopCanonicalVerticalFlux pairing C) with hz | hz
    · exfalso
      apply h
      rw [hz]
      positivity
    · exact hz


theorem sum_fkOrientedMedialLoopVerticalFlux_eq
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T) :
    (∑ C : FKMedialLoop T pairing,
        fkOrientedMedialLoopVerticalFlux pairing arrows C) =
      fkOrientedLoopVerticalFlux T arrows := by
  classical
  unfold fkOrientedMedialLoopVerticalFlux fkOrientedLoopVerticalFlux
    fkOrientedVerticalSeamSign
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp


theorem fkOrientedLoopVerticalFlux_downwardMode
    (pairing : FKMedialLoopPairing T) :
    fkOrientedLoopVerticalFlux T
        (FKMedialTurningFiber.arrowsOfMode pairing
          (fkMedialDownwardVerticalMode pairing)) =
      -(fkMedialUnorientedVerticalWindingTotal pairing : Int) := by
  rw [← sum_fkOrientedMedialLoopVerticalFlux_eq pairing]
  simp_rw [fkOrientedMedialLoopVerticalFlux_downwardMode]
  change (∑ C ∈ (Finset.univ : Finset (FKMedialLoop T pairing)),
      -((fkMedialLoopCanonicalVerticalFlux pairing C).natAbs : Int)) = _
  rw [Finset.sum_neg_distrib]
  congr 1
  unfold fkMedialUnorientedVerticalWindingTotal
  exact (Nat.cast_sum (R := Int)
    (Finset.univ : Finset (FKMedialLoop T pairing))
    (fun C => (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs)).symm


theorem fkOrientedLoopVerticalFlux_eq_downwardMode_of_eq_on_windingComponents
    (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing -> Bool)
    (hmode : forall C, C ∈ fkMedialVerticallyWindingComponents pairing ->
      mode C = fkMedialDownwardVerticalMode pairing C) :
    fkOrientedLoopVerticalFlux T
        (FKMedialTurningFiber.arrowsOfMode pairing mode) =
      -(fkMedialUnorientedVerticalWindingTotal pairing : Int) := by
  rw [← sum_fkOrientedMedialLoopVerticalFlux_eq pairing]
  calc
    (∑ C : FKMedialLoop T pairing,
        fkOrientedMedialLoopVerticalFlux pairing
          (FKMedialTurningFiber.arrowsOfMode pairing mode) C) =
        ∑ C : FKMedialLoop T pairing,
          fkOrientedMedialLoopVerticalFlux pairing
            (FKMedialTurningFiber.arrowsOfMode pairing
              (fkMedialDownwardVerticalMode pairing)) C := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [fkOrientedMedialLoopVerticalFlux_arrowsOfMode,
        fkOrientedMedialLoopVerticalFlux_arrowsOfMode]
      by_cases hflux : fkMedialLoopCanonicalVerticalFlux pairing C = 0
      · simp [hflux]
      · have hmem : C ∈ fkMedialVerticallyWindingComponents pairing := by
          simp [fkMedialVerticallyWindingComponents, hflux]
        rw [hmode C hmem]
    _ = -(fkMedialUnorientedVerticalWindingTotal pairing : Int) := by
      rw [sum_fkOrientedMedialLoopVerticalFlux_eq]
      exact fkOrientedLoopVerticalFlux_downwardMode pairing

theorem even_natAbs_cast_sub_self (z : Int) :
    Even ((z.natAbs : Int) - z) := by
  rw [Int.even_sub', Int.odd_coe_nat, Int.natAbs_odd]


theorem even_fkMedialUnorientedVerticalWindingTotal
    (pairing : FKMedialLoopPairing T) :
    Even (fkMedialUnorientedVerticalWindingTotal pairing) := by
  let arrows := fkMedialCheckerArrows T
  let f := fkOrientedMedialLoopVerticalFlux pairing arrows
  let g : FKMedialLoop T pairing → Int :=
    fun C => Int.ofNat (f C).natAbs - f C
  have habs (C : FKMedialLoop T pairing) :
      (f C).natAbs =
        (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs := by
    exact fkOrientedMedialLoopVerticalFlux_natAbs pairing arrows
      (fkMedialCheckerArrows_compatible T pairing) C
  have hdiff : Even (∑ C : FKMedialLoop T pairing, g C) := by
    apply Finset.even_sum
    intro C hC
    exact even_natAbs_cast_sub_self (f C)
  have hflux : Even (∑ C : FKMedialLoop T pairing, f C) := by
    rw [sum_fkOrientedMedialLoopVerticalFlux_eq]
    rw [fkOrientedLoopVerticalFlux_eq_charge]
    have hwidth : Even (T.width : Int) :=
      (Int.even_coe_nat _).2 T.width_even
    exact (Even.mul_right even_two _).sub hwidth
  have hcast :
      Even ((fkMedialUnorientedVerticalWindingTotal pairing : Nat) : Int) := by
    have hadd := hdiff.add hflux
    simp only [g] at hadd
    rw [Finset.sum_sub_distrib, sub_add_cancel] at hadd
    change Even (Int.ofNat (∑ C : FKMedialLoop T pairing,
      (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs))
    rw [show Int.ofNat (∑ C : FKMedialLoop T pairing,
          (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs) =
        ∑ C : FKMedialLoop T pairing,
          Int.ofNat (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs by
      simpa using Nat.cast_sum (R := Int)
        (Finset.univ : Finset (FKMedialLoop T pairing))
        (fun C => (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs)]
    simpa only [habs] using hadd
  exact (Int.even_coe_nat _).1 hcast


theorem two_mul_half_fkMedialUnorientedVerticalWindingTotal
    (pairing : FKMedialLoopPairing T) :
    2 * (fkMedialUnorientedVerticalWindingTotal pairing / 2) =
      fkMedialUnorientedVerticalWindingTotal pairing := by
  exact Nat.two_mul_div_two_of_even
    (even_fkMedialUnorientedVerticalWindingTotal pairing)


theorem card_fkMedialVerticallyWindingComponents_le_two_of_half_eq_one
    (pairing : FKMedialLoopPairing T)
    (hU : fkMedialUnorientedVerticalWindingTotal pairing / 2 = 1) :
    (fkMedialVerticallyWindingComponents pairing).card ≤ 2 := by
  calc
    (fkMedialVerticallyWindingComponents pairing).card ≤
        fkMedialUnorientedVerticalWindingTotal pairing :=
      card_fkMedialVerticallyWindingComponents_le_total pairing
    _ = 2 * (fkMedialUnorientedVerticalWindingTotal pairing / 2) :=
      (two_mul_half_fkMedialUnorientedVerticalWindingTotal pairing).symm
    _ = 2 := by rw [hU]


theorem natAbs_fkOrientedLoopVerticalFlux_le_unorientedWindingTotal
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v) :
    (fkOrientedLoopVerticalFlux T arrows).natAbs ≤
      fkMedialUnorientedVerticalWindingTotal pairing := by
  rw [← sum_fkOrientedMedialLoopVerticalFlux_eq pairing arrows]
  calc
    (∑ C : FKMedialLoop T pairing,
        fkOrientedMedialLoopVerticalFlux pairing arrows C).natAbs ≤
        ∑ C : FKMedialLoop T pairing,
          (fkOrientedMedialLoopVerticalFlux pairing arrows C).natAbs := by
      simpa using Int.natAbs_sum_le Finset.univ
        (fun C : FKMedialLoop T pairing =>
          fkOrientedMedialLoopVerticalFlux pairing arrows C)
    _ = fkMedialUnorientedVerticalWindingTotal pairing := by
      unfold fkMedialUnorientedVerticalWindingTotal
      apply Finset.sum_congr rfl
      intro C hC
      exact fkOrientedMedialLoopVerticalFlux_natAbs
        pairing arrows hcompat C


theorem two_mul_le_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
    (r : Nat)
    (hflux : fkOrientedLoopVerticalFlux T arrows = -(2 * (r : Int))) :
    2 * r ≤ fkMedialUnorientedVerticalWindingTotal pairing := by
  have hbound :=
    natAbs_fkOrientedLoopVerticalFlux_le_unorientedWindingTotal
      pairing arrows hcompat
  rw [hflux] at hbound
  norm_num at hbound ⊢
  exact hbound


theorem le_half_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
    (r : Nat)
    (hflux : fkOrientedLoopVerticalFlux T arrows = -(2 * (r : Int))) :
    r ≤ fkMedialUnorientedVerticalWindingTotal pairing / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  simpa [mul_comm] using
    two_mul_le_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul
      pairing arrows hcompat r hflux


theorem fkOrientedLoopPairingWeight_ne_zero_iff_compatible
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (arrows : SixVertexArrows T) :
    fkOrientedLoopPairingWeight lam pairing arrows ≠ 0 ↔
      ∀ v, fkLoopPairingCompatible (pairing v) arrows v := by
  classical
  unfold fkOrientedLoopPairingWeight
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro h v
    by_contra hbad
    have hv := h v (Finset.mem_univ v)
    simp [fkOrientedLoopLocalWeight, hbad] at hv
  · intro h v hv
    simp only [fkOrientedLoopLocalWeight, if_pos (h v)]
    split
    · split <;> exact Real.exp_ne_zero _
    · norm_num

theorem fkOrientedLoopPairingWeight_nonneg
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (arrows : SixVertexArrows T) :
    0 ≤ fkOrientedLoopPairingWeight lam pairing arrows := by
  classical
  unfold fkOrientedLoopPairingWeight
  apply Finset.prod_nonneg
  intro v hv
  unfold fkOrientedLoopLocalWeight
  split
  · split
    · split <;> positivity
    · norm_num
  · norm_num


theorem exists_positive_weight_verticalFlux_eq_neg_two_mul_half
    (lam : Real) (pairing : FKMedialLoopPairing T) :
    ∃ arrows : SixVertexArrows T,
      0 < fkOrientedLoopPairingWeight lam pairing arrows ∧
      fkOrientedLoopVerticalFlux T arrows =
        -(2 * ((fkMedialUnorientedVerticalWindingTotal pairing / 2 : Nat) : Int)) := by
  let arrows := FKMedialTurningFiber.arrowsOfMode pairing
    (fkMedialDownwardVerticalMode pairing)
  refine ⟨arrows, ?_, ?_⟩
  · have hne : fkOrientedLoopPairingWeight lam pairing arrows ≠ 0 :=
      (fkOrientedLoopPairingWeight_ne_zero_iff_compatible
        lam pairing arrows).2
        (FKMedialTurningFiber.compatible_arrowsOfMode pairing _)
    exact lt_of_le_of_ne (fkOrientedLoopPairingWeight_nonneg lam pairing arrows)
      (Ne.symm hne)
  · have hhalf :=
      two_mul_half_fkMedialUnorientedVerticalWindingTotal pairing
    have hcast : (fkMedialUnorientedVerticalWindingTotal pairing : Int) =
        2 * ((fkMedialUnorientedVerticalWindingTotal pairing / 2 : Nat) : Int) := by
      exact_mod_cast hhalf.symm
    rw [show fkOrientedLoopVerticalFlux T arrows =
        -(fkMedialUnorientedVerticalWindingTotal pairing : Int) by
      exact fkOrientedLoopVerticalFlux_downwardMode pairing]
    rw [hcast]

end
end StatMech.FrontierD
