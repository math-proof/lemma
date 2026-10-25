/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

theorem eq_of_sameCycle_of_step
    {A B : Type*} [Fintype A] [DecidableEq A]
    (sigma : Equiv.Perm A) (f : A → B)
    (hstep : ∀ x, f (sigma x) = f x) {x y : A}
    (hxy : sigma.SameCycle x y) : f x = f y := by
  obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
  have hpow : ∀ m : Nat, f ((sigma ^ m) x) = f x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, hstep]
        exact ih
  calc
    f x = f ((sigma ^ k) x) := (hpow k).symm
    _ = f y := congrArg f hk

theorem fkIsingSquareInteriorRadialDart_ne_source
    (n : Nat) (hn : 0 < n)
    (d : FKIsingSquareInteriorRadialDart n) :
    d.1 ≠ fkIsingSquareWiredSourceDart n hn := by
  intro h
  have hi := d.2
  rw [h] at hi
  exact fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn .bottom hi

theorem fkIsingSquareInteriorRadialDart_ne_terminal
    (n : Nat) (hn : 0 < n)
    (d : FKIsingSquareInteriorRadialDart n) :
    d.1 ≠ fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have hi := d.2
  rw [h] at hi
  exact fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn .top hi

theorem fkIsingSquareSignedEighthTurn_eq_zero_of_modEq
    (a b : Int) (h : a ≡ b [ZMOD 8]) :
    fkIsingSquareSignedEighthTurn a b = 0 := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  have heq : b - a + 4 = 8 * k + 4 := by omega
  unfold fkIsingSquareSignedEighthTurn
  rw [heq, Int.add_emod, Int.mul_emod]
  norm_num


theorem fkIsingSquareInteriorRadial_bondTurn_eq_zero_of_directedTangentCode_eq
    (n : Nat) (hn : 0 < n) (d : FKIsingSquareInteriorRadialDart n)
    (hcode : fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]) :
    fkIsingSquareWiredBondTurn n hn d.1
        (fkIsingSquareInteriorRadialBondMate n hn d).1 = 0 := by
  let f := fkIsingSquareInteriorRadialBondMate n hn d
  have hdsource := fkIsingSquareInteriorRadialDart_ne_source n hn d
  have hfsource := fkIsingSquareInteriorRadialDart_ne_source n hn f
  have hforward : ¬ fkIsingSquareWiredBoundaryForward n hn d.1 f.1 := by
    intro h
    rcases h with h | ⟨k, hd, _hf⟩
    · exact hdsource h.1
    · have hi := d.2
      rw [hd] at hi
      exact fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn (.west k) hi
  have hreverse : ¬ fkIsingSquareWiredBoundaryReverse n hn d.1 f.1 := by
    intro h
    rcases h with h | ⟨k, hf, _hd⟩
    · exact hfsource h.1
    · have hi := f.2
      rw [hf] at hi
      exact fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn (.west k) hi
  rw [fkIsingSquareWiredBondTurn, if_neg hforward, if_neg hreverse]
  change fkIsingSquareOrientedPrincipalBondTurn n hn d.1 f.1 = 0
  have hturn := fkIsingSquareWiredBondMate_turn_ne n hn d.1
  change (fkIsingSquareSideCorner f.1.2).2 ≠
      (fkIsingSquareSideCorner d.1.2).2 at hturn
  change fkIsingSquareWiredDirectedTangentCode n hn (.bond f.1) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] at hcode
  cases hdturn : (fkIsingSquareSideCorner d.1.2).2 <;>
    cases hfturn : (fkIsingSquareSideCorner f.1.2).2
  · exact False.elim (hturn (hfturn.trans hdturn.symm))
  · simp only [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection, hdturn, hfturn] at hcode
    have hmod :
        fkIsingSquareWiredCarrierTangentCode n hn (.bond d.1) ≡
          fkIsingSquareWiredCarrierTangentCode n hn (.bond f.1) + 4 [ZMOD 8] := by
      simpa using hcode.symm
    have hraw := fkIsingSquareSignedEighthTurn_eq_zero_of_modEq
      (fkIsingSquareWiredCarrierTangentCode n hn (.bond d.1))
      (fkIsingSquareWiredCarrierTangentCode n hn (.bond f.1) + 4)
      hmod
    simp [fkIsingSquareOrientedPrincipalBondTurn, hdturn, hfturn, hraw]
  · simp only [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection, hdturn, hfturn] at hcode
    have hplus := hcode.add (Int.ModEq.refl 4)
    have hwrap :
        fkIsingSquareWiredCarrierTangentCode n hn (.bond d.1) + 4 + 4 ≡
          fkIsingSquareWiredCarrierTangentCode n hn (.bond d.1) [ZMOD 8] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨-1, by ring⟩
    have hmod :
        fkIsingSquareWiredCarrierTangentCode n hn (.bond d.1) ≡
          fkIsingSquareWiredCarrierTangentCode n hn (.bond f.1) + 4 [ZMOD 8] := by
      simpa using (hplus.trans hwrap).symm
    have hraw := fkIsingSquareSignedEighthTurn_eq_zero_of_modEq
      (fkIsingSquareWiredCarrierTangentCode n hn (.bond d.1))
      (fkIsingSquareWiredCarrierTangentCode n hn (.bond f.1) + 4)
      hmod
    simp [fkIsingSquareOrientedPrincipalBondTurn, hdturn, hfturn, hraw]
  · exact False.elim (hturn (hfturn.trans hdturn.symm))


theorem fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
    (n : Nat) (hn : 0 < n) (d : FKIsingSquareInteriorRadialDart n)
    (hcode : fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareInteriorRadialBondMate n hn d).1) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) := by
  have hturn :=
    fkIsingSquareInteriorRadial_bondTurn_eq_zero_of_directedTangentCode_eq
      n hn d hcode
  have hphase : fkIsingSquareWiredBondPhase n hn d.1 = 1 := by
    unfold fkIsingSquareWiredBondPhase
    rw [show fkIsingSquareWiredBondTurn n hn d.1
        (fkIsingSquareWiredBondMate n hn d.1) = 0 by exact hturn]
    norm_num
  calc
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareInteriorRadialBondMate n hn d).1) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d).1) := by
      rw [fkIsingSquareWired_fermionicObservable_incidence]
    _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.bond d.1) * fkIsingSquareWiredBondPhase n hn d.1 := by
      exact fkIsingSquareWired_fermionicObservable_bondMate n hn d.1
        (fkIsingSquareInteriorRadialDart_ne_source n hn d)
        (fkIsingSquareInteriorRadialDart_ne_terminal n hn d)
    _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart d.1) := by
      rw [hphase, mul_one, fkIsingSquareWired_fermionicObservable_incidence]

theorem fkIsingSquareInteriorRadial_endpoint_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingSquareInteriorRadialDart n) :
    fkIsingSquareDartEndpoint n
        (fkIsingSquareInteriorRadialBondMate n hn d).1 =
      fkIsingSquareDartEndpoint n d.1 := by
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBondMate n hn d.1) = _
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2]
  exact fkIsingSquareDartEndpoint_bondMate n hn d.1

theorem fkIsingSquareInteriorRadial_faceKey_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingSquareInteriorRadialDart n) :
    fkIsingSquareWedgeFaceKey n
        (fkIsingSquareInteriorRadialBondMate n hn d).1 =
      fkIsingSquareWedgeFaceKey n d.1 := by
  change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareWiredBondMate n hn d.1) = _
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2]
  exact fkIsingSquareWedgeFaceKey_bondMate n hn d.1 d.2

theorem fkIsingSquareInteriorRadial_increment_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingSquareInteriorRadialDart n) :
    fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquareInteriorRadialBondMate n hn d).1) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart d.1) := by
  change fkIsingSquareWiredPrimitiveIncrement n hn
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _
  exact fkIsingSquareWiredPrimitiveIncrement_bondDartMate n hn d.1
    (fkIsingSquareInteriorRadialDart_ne_source n hn d)
    (fkIsingSquareInteriorRadialDart_ne_terminal n hn d)


end
end StatMech.Universality
