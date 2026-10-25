/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalIncidence
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond


namespace StatMech.Universality

open SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredBondPhase_normSq
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    Complex.normSq (fkIsingSquareWiredBondPhase n hn d) = 1 := by
  rw [Complex.normSq_eq_norm_sq, fkIsingSquareWiredBondPhase,
    Complex.norm_exp]
  simp

theorem fkIsingSquareWired_fermionicSummand_bondMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
          (.bond d) * fkIsingSquareWiredBondPhase n hn d := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  have hmem := fkIsingSquareWired_bondMate_mem_trace_iff
    n hn omega d hsource hterminal
  by_cases hd : (.bond d : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn omega
  · have hf := hmem.mpr hd
    have horder : (.bond d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationOrder n hn omega := by
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact hd
    have hwind := fkIsingSquareWiredLiftedWinding_bondMate
      n hn omega d hsource hterminal horder
    simp only [FKIsingDobrushinDomain.fermionicSummand, D,
      fkIsingSquareWiredDobrushinDomain, hf, hd, if_true,
      FKIsingDobrushinDomain.windingPhase]
    rw [hwind]
    unfold fkIsingSquareWiredBondPhase
    rw [show Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega (.bond d) +
              (fkIsingSquareWiredBondTurn n hn d
                (fkIsingSquareWiredBondMate n hn d) : Real) *
                  (Real.pi / 4)) / 2 : Real) : Complex) =
        Complex.I *
            ((fkIsingSquareWiredLiftedWinding n hn omega (.bond d) / 2 : Real) :
              Complex) +
          Complex.I *
            ((((fkIsingSquareWiredBondTurn n hn d
              (fkIsingSquareWiredBondMate n hn d) : Int) : Real) *
                (Real.pi / 8) : Real) : Complex) by push_cast; ring,
      Complex.exp_add]
    ring
  · have hf : (.bond (fkIsingSquareWiredBondMate n hn d) :
        FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn omega := by
      exact fun h ↦ hd (hmem.mp h)
    simp [FKIsingDobrushinDomain.fermionicSummand, D,
      fkIsingSquareWiredDobrushinDomain, hf, hd]

theorem fkIsingSquareWired_fermionicObservable_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.bond d) *
        fkIsingSquareWiredBondPhase n hn d := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro omega _
  exact fkIsingSquareWired_fermionicSummand_bondMate
    n hn omega d hsource hterminal

theorem fkIsingSquareWiredPrimitiveIncrement_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    fkIsingSquareWiredPrimitiveIncrement n hn
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.bond d) := by
  unfold fkIsingSquareWiredPrimitiveIncrement isingPrimitiveIncrement
  rw [fkIsingSquareWired_fermionicObservable_bondMate n hn d
    hsource hterminal, Complex.normSq_mul,
    fkIsingSquareWiredBondPhase_normSq, mul_one]


theorem fkIsingSquareWiredPrimitiveIncrement_bondDartMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquareWiredBondMate n hn d)) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart d) := by
  rw [← fkIsingSquareWiredPrimitiveIncrement_incidence n hn
      (fkIsingSquareWiredBondMate n hn d),
    fkIsingSquareWiredPrimitiveIncrement_bondMate n hn d
      hsource hterminal,
    fkIsingSquareWiredPrimitiveIncrement_incidence]


theorem fkIsingSquareWiredPrimitiveIncrement_bond_local_closed
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredPrimitiveIncrement n hn (.bond (e, .west)) +
        fkIsingSquareWiredPrimitiveIncrement n hn (.bond (e, .east)) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.bond (e, .south)) +
        fkIsingSquareWiredPrimitiveIncrement n hn (.bond (e, .north)) := by
  simp only [fkIsingSquareWiredPrimitiveIncrement_incidence]
  exact fkIsingSquareWiredPrimitiveIncrement_local_closed n hn e

end
end StatMech.Universality
