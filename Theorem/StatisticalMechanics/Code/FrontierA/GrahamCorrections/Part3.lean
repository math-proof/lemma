/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Def.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3


namespace StatMech.FrontierA

open Finset

open scoped symmDiff

open StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem grahamCorrectedRHS_eq (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) :
    grahamCorrectedRHS E J i j k l m =
      -2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m *
        grahamTwoPoint E J k m * grahamTwoPoint E J l m)
      + -2 * (grahamBridgeGap E J i k m * grahamBridgeGap E J j k m *
        grahamTwoPoint E J k l)
      + -2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m *
        grahamBridgeGap E J i k m * grahamBridgeGap E J i l m) :=
  rfl


theorem grahamTwoPoint_nonneg (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (x y : V) :
    0 ≤ grahamTwoPoint E J x y := by
  exact ghsvp_expJ_zero_nonneg E J hJ (grahamPairSupport x y)


theorem grahamBridgeGap_nonneg (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i k m : V) :
    0 ≤ grahamBridgeGap E J i k m := by
  rw [grahamBridgeGap, sub_nonneg]
  have h := gks_second_J E J (fun _ => 0) hJ (fun _ => le_rfl)
    (grahamPairSupport i m) (grahamPairSupport m k)
  rw [grahamPairSupport_chain] at h
  exact h


theorem grahamLeadingTerm_nonpos (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i j k l m : V) :
    grahamLeadingTerm E J i j k l m ≤ 0 := by
  have hprod : 0 ≤ grahamTwoPoint E J i m * grahamTwoPoint E J j m *
      grahamTwoPoint E J k m * grahamTwoPoint E J l m :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (grahamTwoPoint_nonneg E J hJ i m)
          (grahamTwoPoint_nonneg E J hJ j m))
        (grahamTwoPoint_nonneg E J hJ k m))
      (grahamTwoPoint_nonneg E J hJ l m)
  unfold grahamLeadingTerm
  nlinarith


theorem grahamKCorrection_nonpos (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i j k l m : V) :
    grahamKCorrection E J i j k l m ≤ 0 := by
  have hprod : 0 ≤ grahamBridgeGap E J i k m * grahamBridgeGap E J j k m *
      grahamTwoPoint E J k l :=
    mul_nonneg
      (mul_nonneg (grahamBridgeGap_nonneg E J hJ i k m)
        (grahamBridgeGap_nonneg E J hJ j k m))
      (grahamTwoPoint_nonneg E J hJ k l)
  unfold grahamKCorrection
  nlinarith


theorem grahamICorrection_nonpos (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i j k l m : V) :
    grahamICorrection E J i j k l m ≤ 0 := by
  have hprod : 0 ≤ grahamTwoPoint E J i m * grahamTwoPoint E J j m *
      grahamBridgeGap E J i k m * grahamBridgeGap E J i l m :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (grahamTwoPoint_nonneg E J hJ i m)
          (grahamTwoPoint_nonneg E J hJ j m))
        (grahamBridgeGap_nonneg E J hJ i k m))
      (grahamBridgeGap_nonneg E J hJ i l m)
  unfold grahamICorrection
  nlinarith


theorem grahamCorrectedRHS_le_leading (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i j k l m : V) :
    grahamCorrectedRHS E J i j k l m ≤ grahamLeadingTerm E J i j k l m := by
  have hk := grahamKCorrection_nonpos E J hJ i j k l m
  have hi := grahamICorrection_nonpos E J hJ i j k l m
  unfold grahamCorrectedRHS
  linarith


theorem grahamCorrectedRHS_nonpos (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i j k l m : V) :
    grahamCorrectedRHS E J i j k l m ≤ 0 :=
  (grahamCorrectedRHS_le_leading E J hJ i j k l m).trans
    (grahamLeadingTerm_nonpos E J hJ i j k l m)


theorem grahamCorrectedRHS_aux_eq_l (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l : V) :
    grahamCorrectedRHS E J i j k l l =
      -2 * (grahamTwoPoint E J i l * grahamTwoPoint E J j l *
        grahamTwoPoint E J k l)
      + -2 * (grahamBridgeGap E J i k l * grahamBridgeGap E J j k l *
        grahamTwoPoint E J k l) := by
  simp [grahamCorrectedRHS, grahamLeadingTerm, grahamKCorrection,
    grahamICorrection, grahamBridgeGap]

end StatMech.FrontierA
