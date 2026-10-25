/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedMomentBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part2
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

namespace PhysicalIsing

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem finiteIsingWeightedRawMoment_zero
    (beta : Real) (a : V -> Real) :
    finiteIsingWeightedRawMoment G beta a 0 = 1 := by
  unfold finiteIsingWeightedRawMoment
  simp only [pow_zero, mul_one]
  apply div_self
  exact ne_of_gt (Finset.sum_pos
    (fun s _ => by unfold zeroFieldInteractionWeight; positivity)
    Finset.univ_nonempty)


theorem finiteIsingWeightedRawMoment_odd
    (beta : Real) (a : V -> Real) (order : Nat) (horder : Odd order) :
    finiteIsingWeightedRawMoment G beta a order = 0 := by
  have hderiv := iteratedDeriv_zero_of_even_of_odd
    (finiteIsingWeightedMomentGeneratingFunction G beta a)
    (finiteIsingWeightedMomentGeneratingFunction_neg G beta a)
    order horder
  rw [iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero_eq_rawMoment]
    at hderiv
  exact_mod_cast hderiv


theorem finiteIsingWeighted_hasScalarMomentCumulantRecurrence
    (beta : Nat -> Real) (a : (scale : Nat) -> V -> Real) :
    HasScalarMomentCumulantRecurrence
      (fun scale => finiteIsingWeightedRawMoment G (beta scale) (a scale))
      (fun scale => finiteIsingWeightedCumulant G (beta scale) (a scale)) := by
  exact hasScalarMomentCumulantRecurrence_cumulantsOfMoments _
    (fun scale => finiteIsingWeightedRawMoment_zero G (beta scale) (a scale))

theorem finiteIsingWeightedCumulant_zero
    (beta : Real) (a : V -> Real) :
    finiteIsingWeightedCumulant G beta a 0 = 0 := by
  unfold finiteIsingWeightedCumulant
  rw [scalarCumulantsOfMoments_zero]

theorem finiteIsingWeightedCumulant_odd
    (beta : Real) (a : V -> Real) (order : Nat) (horder : Odd order) :
    finiteIsingWeightedCumulant G beta a order = 0 := by
  unfold finiteIsingWeightedCumulant
  exact scalarCumulantsOfMoments_odd _
    (finiteIsingWeightedRawMoment_odd G beta a) order horder


theorem finiteIsingWeighted_scaledCumulants
    (beta : Real) (a : V -> Real) (c : Real) (order : Nat) :
    scalarCumulantsOfMoments
        (fun m => c ^ m * finiteIsingWeightedRawMoment G beta a m) order =
      c ^ order * finiteIsingWeightedCumulant G beta a order := by
  exact scalarCumulantsOfMoments_scale
    (finiteIsingWeightedRawMoment G beta a) c order


theorem finiteIsingWeightedCumulant_two_eq_parity
    (beta : Real) (a : V -> Real) :
    finiteIsingWeightedCumulant G beta a 2 =
      finiteWeightedParitySecondMoment G beta (fun _ => 1) a := by
  unfold finiteIsingWeightedCumulant
  rw [scalarCumulantsOfMoments_two,
    finiteIsingWeightedRawMoment_odd G beta a 1 (by exact ⟨0, rfl⟩),
    finiteIsingWeightedRawMoment_two_eq_parity]
  ring


theorem finiteIsingWeightedCumulant_four_eq_parity
    (beta : Real) (a : V -> Real) :
    finiteIsingWeightedCumulant G beta a 4 =
      finiteWeightedParityFourthCumulant G beta (fun _ => 1) a := by
  unfold finiteIsingWeightedCumulant
  rw [scalarCumulantsOfMoments_four_of_symmetric
      (finiteIsingWeightedRawMoment G beta a)
      (finiteIsingWeightedRawMoment_odd G beta a 1 (by exact ⟨0, rfl⟩))
      (finiteIsingWeightedRawMoment_odd G beta a 3 (by exact ⟨1, rfl⟩)),
    scalarFourthCumulant_finiteIsingWeightedRawMoment_eq]


theorem criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled
    (d n : Nat) (a : sctBox d n -> Real) (c : Real)
    (hc : c ^ 4 = 1 /
      (2 * (Fintype.card (sctBox d n) : Real) *
        criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
        ((2 * n + 1 : Nat) : Real) ^ d)) :
    criticalFiniteBoxWeightedNormalizedFourthCumulant d n a =
      scalarCumulantsOfMoments
        (fun order => c ^ order *
          finiteIsingWeightedRawMoment
            (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) a order) 4 := by
  rw [finiteIsingWeighted_scaledCumulants,
    finiteIsingWeightedCumulant_four_eq_parity]
  unfold criticalFiniteBoxWeightedNormalizedFourthCumulant
    criticalFiniteBoxWeightedParityFourthCumulant
  rw [hc]
  ring


theorem exists_criticalFiniteBoxWeightedFourthScale
    (d n : Nat) (hd : 2 <= d) :
    ∃ c : Real, 0 < c ∧ c ^ 4 = 1 /
      (2 * (Fintype.card (sctBox d n) : Real) *
        criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
        ((2 * n + 1 : Nat) : Real) ^ d) := by
  let denominator : Real :=
    2 * (Fintype.card (sctBox d n) : Real) *
      criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
      ((2 * n + 1 : Nat) : Real) ^ d
  have hcard : 0 < (Fintype.card (sctBox d n) : Real) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨criticalFiniteBoxOrigin d n⟩
  have hchi : 0 < criticalFreeBoxSusceptibility d (2 * n) := by
    linarith [one_le_criticalFreeBoxSusceptibility hd (2 * n)]
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  let x : Real := 1 / denominator
  let c : Real := Real.sqrt (Real.sqrt x)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hsqrtx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hc : 0 < c := by
    dsimp [c]
    exact Real.sqrt_pos.2 hsqrtx
  refine ⟨c, hc, ?_⟩
  have hcSquare : c ^ 2 = Real.sqrt x := by
    dsimp [c]
    exact Real.sq_sqrt hsqrtx.le
  have hxSquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  change c ^ 4 = x
  calc
    c ^ 4 = (c ^ 2) ^ 2 := by ring
    _ = (Real.sqrt x) ^ 2 := by rw [hcSquare]
    _ = x := hxSquare


end PhysicalIsing
end
end StatMech.FrontierA
