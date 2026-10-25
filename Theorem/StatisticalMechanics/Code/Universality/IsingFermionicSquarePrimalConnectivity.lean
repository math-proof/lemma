/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareSourcePhase.Part2
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

theorem fkIsingSquare_openWiredExteriorGadget_reachable_iff
    (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : (fkSquareBoxPlanar n).V) :
    (fkIsingSquareLiftPhysicalGraph n
          (openSub (fkSquareBoxPlanar n).G omega) ⊔
        fkIsingSquareWiredExteriorGadget n).Reachable
        (.physical x) (.physical y) ↔
      (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable x y :=
  fkIsingSquare_wiredExteriorGadget_reachable_iff_clique n
    (openSub (fkSquareBoxPlanar n).G omega) x y


theorem fkIsingSquare_caseThree_westNorth_contour_algebra
    (m cW cE cS cN oW oN : Complex)
    (hcS : cS = isingLambda⁻¹ * cW)
    (hcN : cN = isingLambda⁻¹ * cE)
    (hoN : oN = isingLambda * oW)
    (hterminal : oN = cN) (hsource : oW = cW) :
    (m * cW + (Real.sqrt 2 : Complex) * m * oW) - m * cE =
      Complex.I *
        (m * cS - (m * cN + (Real.sqrt 2 : Complex) * m * oN)) := by
  have hcE : cE = isingLambda ^ 2 * cW := by
    calc
      cE = isingLambda * (isingLambda⁻¹ * cE) := by
        field_simp [isingLambda_ne]
      _ = isingLambda * cN := by rw [← hcN]
      _ = isingLambda * oN := by rw [hterminal]
      _ = isingLambda * (isingLambda * oW) := by rw [hoN]
      _ = isingLambda ^ 2 * cW := by rw [hsource]; ring
  rw [hterminal, hcS, hcN, hsource, hcE,
    isingLambda_inv, isingLambda_sq, isingLambda_val]
  field_simp [isingSqrt2_ne]
  ring_nf
  rw [isingSqrt2_sq, Complex.I_sq]
  have hs3 : (Real.sqrt 2 : Complex) ^ 3 =
      2 * (Real.sqrt 2 : Complex) := by
    rw [show (3 : Nat) = 2 + 1 by omega, pow_succ, isingSqrt2_sq]
  rw [hs3, show Complex.I ^ 3 = -Complex.I by
    rw [pow_succ, Complex.I_sq]; ring]
  ring


theorem fkIsingSquare_caseThree_eastSouth_contour_algebra
    (m cW cE cS cN oE oS : Complex)
    (hcS : cS = isingLambda⁻¹ * cW)
    (hcN : cN = isingLambda⁻¹ * cE)
    (hoS : oS = isingLambda * oE)
    (hterminal : oS = cS) (hsource : oE = cE) :
    m * cW - (m * cE + (Real.sqrt 2 : Complex) * m * oE) =
      Complex.I *
        ((m * cS + (Real.sqrt 2 : Complex) * m * oS) - m * cN) := by
  have hcW : cW = isingLambda ^ 2 * cE := by
    calc
      cW = isingLambda * (isingLambda⁻¹ * cW) := by
        field_simp [isingLambda_ne]
      _ = isingLambda * cS := by rw [← hcS]
      _ = isingLambda * oS := by rw [hterminal]
      _ = isingLambda * (isingLambda * oE) := by rw [hoS]
      _ = isingLambda ^ 2 * cE := by rw [hsource]; ring
  rw [hterminal, hcS, hcN, hsource, hcW,
    isingLambda_inv, isingLambda_sq, isingLambda_val]
  field_simp [isingSqrt2_ne]
  ring_nf
  rw [isingSqrt2_sq, Complex.I_sq]
  have hs3 : (Real.sqrt 2 : Complex) ^ 3 =
      2 * (Real.sqrt 2 : Complex) := by
    rw [show (3 : Nat) = 2 + 1 by omega, pow_succ, isingSqrt2_sq]
  rw [hs3, show Complex.I ^ 3 = -Complex.I by
    rw [pow_succ, Complex.I_sq]; ring]
  ring


end
end StatMech.Universality
