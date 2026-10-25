/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part3


namespace StatMech.Universality

open Filter Set Topology Metric

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

theorem fkIsingSquareSitePosition_neighbor
    (n : Nat) (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareSitePosition (fkIsingSquareNeighbor n u d hd).1 =
      fkIsingSquareSitePosition u.1 + fkIsingSquareDirectionComplexStep d := by
  cases d <;> apply Complex.ext <;>
    simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareSitePosition, fkIsingSquareDirectionComplexStep] <;> rfl

theorem fkIsingSquareDirectionComplexStep_norm
    (d : FKIsingSquareDirection) :
    ‖fkIsingSquareDirectionComplexStep d‖ = 1 := by
  cases d <;> simp [fkIsingSquareDirectionComplexStep]

theorem fkIsingSquareDirectionEdgeOrientation_position_sum
    (n : Nat) (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareSitePosition
          (fkIsingSquareDirectionEdgeOrientation n u d hd).tail.1 +
        fkIsingSquareSitePosition
          (fkIsingSquareDirectionEdgeOrientation n u d hd).head.1 =
      fkIsingSquareSitePosition u.1 +
        fkIsingSquareSitePosition (fkIsingSquareNeighbor n u d hd).1 := by
  cases d <;>
    simp [fkIsingSquareDirectionEdgeOrientation] <;> ac_rfl

set_option maxHeartbeats 800000 in


theorem fkIsingSquareRadialPatchWindowCarrier_scaledPosition_norm_le
    (n m baseI baseJ R : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (p : IsingLeapfrogBox R) :
    ‖((1 / (m : Real) : Real) : Complex) *
        fkIsingSquareWiredCarrierPosition n (by omega)
          (fkIsingSquareRadialPatchWindowCarrier
            n m baseI baseJ R hm hfitI hfitJ p)‖ ≤ 3 := by
  let i : Fin m := ⟨baseI + p.1.1, by have := p.1.2; omega⟩
  let j : Fin m := ⟨baseJ + p.2.1, by have := p.2.2; omega⟩
  let u := fkIsingSquareRadialPatchVertex n m hm i j
  let d := fkIsingSquareRadialPatchDirection i.1 j.1
  let v := fkIsingSquareNeighbor n u d
    (fkIsingSquareRadialPatchDirection_available n m hm i j)
  have hu0 : |((u.1 0 : Int) : Real)| ≤ (m : Real) := by
    simp [u, fkIsingSquareRadialPatchVertex]
    rw [fkIsingSquareRadialPatchHalf_eq]
    have hi := i.2
    have hj := j.2
    omega
  have hu1 : |((u.1 1 : Int) : Real)| ≤ (m : Real) := by
    have hu1eq : u.1 1 = (i.1 : Int) -
        (((i.1 + j.1 + 1) / 2 : Nat) : Int) := by
      simp only [u, fkIsingSquareRadialPatchVertex]
      rw [fkIsingSquareRadialPatchHalf_eq]
      rfl
    rw [hu1eq]
    have hi := i.2
    have hj := j.2
    have hInt : |(i.1 : Int) - (((i.1 + j.1 + 1) / 2 : Nat) : Int)| ≤
        (m : Int) := by
      rw [abs_le]
      constructor <;> push_cast <;> omega
    exact_mod_cast hInt
  have hupos : ‖fkIsingSquareSitePosition u.1‖ ≤ 2 * (m : Real) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [fkIsingSquareSitePosition]
    linarith
  have hvpos : ‖fkIsingSquareSitePosition v.1‖ ≤ 2 * (m : Real) + 1 := by
    have hvEq : fkIsingSquareSitePosition v.1 = fkIsingSquareSitePosition u.1 +
        fkIsingSquareDirectionComplexStep d :=
      fkIsingSquareSitePosition_neighbor n u d _
    have hstep := fkIsingSquareDirectionComplexStep_norm d
    calc
      ‖fkIsingSquareSitePosition v.1‖ =
          ‖fkIsingSquareSitePosition u.1 +
            fkIsingSquareDirectionComplexStep d‖ := by rw [hvEq]
      _ ≤ ‖fkIsingSquareSitePosition u.1‖ +
          ‖fkIsingSquareDirectionComplexStep d‖ := norm_add_le _ _
      _ = ‖fkIsingSquareSitePosition u.1‖ + 1 := by rw [hstep]
      _ ≤ 2 * (m : Real) + 1 := by linarith
  have hcarrier :
      fkIsingSquareWiredCarrierPosition n (by omega)
          (fkIsingSquareRadialPatchWindowCarrier
            n m baseI baseJ R hm hfitI hfitJ p) =
        (fkIsingSquareSitePosition u.1 + fkIsingSquareSitePosition v.1) / 2 := by
    change (fkIsingSquareSitePosition
        (fkIsingSquareOrientedEdge n
          (fkIsingSquareRadialPatchEdge n m hm i j)).tail.1 +
      fkIsingSquareSitePosition
        (fkIsingSquareOrientedEdge n
          (fkIsingSquareRadialPatchEdge n m hm i j)).head.1) / 2 = _
    rw [fkIsingSquareRadialPatchEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    exact congrArg (fun z : Complex ↦ z / 2)
      (fkIsingSquareDirectionEdgeOrientation_position_sum n u d _)
  rw [hcarrier]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : Real) < 1 / (m : Real))]
  calc
    (1 / (m : Real)) *
        ‖(fkIsingSquareSitePosition u.1 + fkIsingSquareSitePosition v.1) / 2‖ ≤
      (1 / (m : Real)) *
        ((‖fkIsingSquareSitePosition u.1‖ +
          ‖fkIsingSquareSitePosition v.1‖) / 2) := by
      gcongr
      rw [norm_div]
      norm_num
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ (1 / (m : Real)) *
        ((2 * (m : Real) + (2 * (m : Real) + 1)) / 2) := by
      gcongr
    _ ≤ 3 := by
      have hmpos : (0 : Real) < m := by positivity
      have hmone : (1 : Real) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      field_simp
      nlinarith


end
end StatMech.Universality
