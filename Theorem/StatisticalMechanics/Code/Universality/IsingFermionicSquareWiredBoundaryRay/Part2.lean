/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryRay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredBoundaryPhase
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredBoundaryRay.Part2


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredDirectedTangent_mul_phase_sq
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredDirectedTangent n hn z *
        fkIsingSquareWiredDirectedPhase n hn z ^ 2 = 1 := by
  unfold fkIsingSquareWiredDirectedTangent
    fkIsingSquareWiredDirectedPhase
  rw [pow_two, ← Complex.exp_add, ← Complex.exp_add]
  convert Complex.exp_zero
  push_cast
  ring


theorem fkIsingSquareWired_windingPhase_sq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n)
    (hz : z ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase omega z ^ 2 =
      fkIsingSquareWiredDirectedPhase n hn z ^ 2 := by
  have hturn := fkIsingSquareWiredPhysicalTurnCount_modEq_directedTangent
    n hn omega z hz
  calc
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase omega z ^ 2 =
        Complex.exp (Complex.I *
          ((((fkIsingSquareWiredPhysicalTurnCount n hn omega z : Int) : Real) *
            (Real.pi / 4) : Real) : Complex)) := by
      unfold FKIsingDobrushinDomain.windingPhase
        fkIsingSquareWiredDobrushinDomain fkIsingSquareWiredLiftedWinding
      rw [pow_two, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = Complex.exp (Complex.I *
          ((((fkIsingSquareWiredDirectedTangentCode n hn z -
            fkIsingSquareWiredDirectedTangentCode n hn .terminal : Int) : Real) *
              (Real.pi / 4) : Real) : Complex)) :=
      fkIsingSquare_exp_turn_modEq_eight _ _ hturn
    _ = fkIsingSquareWiredDirectedPhase n hn z ^ 2 := by
      unfold fkIsingSquareWiredDirectedPhase
      rw [pow_two, ← Complex.exp_add]
      congr 1
      push_cast
      ring


theorem fkIsingSquareWired_exists_nonnegative_directed_square
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) :
    ∃ t : Real, 0 ≤ t ∧
      fkIsingSquareWiredDirectedTangent n hn z *
          (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable z ^ 2 =
        (t : Complex) := by
  apply (fkIsingSquareWiredDobrushinDomain n hn).exists_nonnegative_boundary_square_of_phase_sq z
      (fkIsingSquareWiredDirectedTangent n hn z)
      (fkIsingSquareWiredDirectedPhase n hn z) 1
  · intro omega hz
    apply fkIsingSquareWired_windingPhase_sq n hn omega z
    rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [fkIsingSquareWiredDobrushinDomain] using hz
  · exact zero_le_one
  · exact fkIsingSquareWiredDirectedTangent_mul_phase_sq n hn z

end
end StatMech.Universality
