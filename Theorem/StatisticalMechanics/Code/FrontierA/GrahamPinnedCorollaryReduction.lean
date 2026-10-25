/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedFieldAdapter.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMarkedSiteCorollary
open Finset
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.ConfigSpace StatMech.Ising StatMech.Sharpness

open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem vbg_exp_grahamZeroProb_mul_spin_eq_zero_of_flipInvariant
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V)
    (F : ConfigSpace V -> Real)
    (hF : forall s, F (FieldGhostDict.flipV s) = F s) :
    vbg_exp (grahamZeroProb E J)
      (fun s => F s * spin s m) = 0 := by
  let S := vbg_exp (grahamZeroProb E J) (fun s => F s * spin s m)
  have hweight : forall s : ConfigSpace V,
      grahamZeroProb E J (FieldGhostDict.flipV s) =
        grahamZeroProb E J s := by
    intro s
    unfold grahamZeroProb
    rw [show wJ E J (fun _ => 0) (FieldGhostDict.flipV s) =
        wJ E J (fun _ => 0) s by
      simpa only [Pi.neg_apply, neg_zero] using
        ghsvp_wJ_negField_flip E J (fun _ => 0) s]
  have hneg : S = -S := by
    have hS : S = ∑ s : ConfigSpace V,
        grahamZeroProb E J (FieldGhostDict.flipV s) *
          (F (FieldGhostDict.flipV s) *
            spin (FieldGhostDict.flipV s) m) :=
      (Equiv.sum_comp
        (FieldGhostDict.flipV_involutive (V := V)).toPerm
        (fun s : ConfigSpace V =>
          grahamZeroProb E J s * (F s * spin s m))).symm
    simp_rw [hweight, hF, FieldGhostDict.spin_flipV] at hS
    rw [show (∑ s : ConfigSpace V,
        grahamZeroProb E J s * (F s * -spin s m)) = -S by
      unfold S vbg_exp
      calc
        (∑ s : ConfigSpace V,
            grahamZeroProb E J s * (F s * -spin s m)) =
            ∑ s : ConfigSpace V,
              -(grahamZeroProb E J s * (F s * spin s m)) := by
                apply sum_congr rfl
                intro s _
                ring
        _ = -(∑ s : ConfigSpace V,
              grahamZeroProb E J s * (F s * spin s m)) := by
                simpa using sum_neg_distrib
        _ = _ := rfl] at hS
    exact hS
  dsimp only [S] at hneg
  linarith


theorem vbg_exp_grahamPinnedProb_eq_of_flipInvariant
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V)
    (F : ConfigSpace V -> Real)
    (hF : forall s, F (FieldGhostDict.flipV s) = F s) :
    vbg_exp (grahamPinnedProb E J m) F =
      expJ E J (fun _ => 0) F := by
  rw [vbg_exp_grahamPinnedProb,
    vbg_exp_grahamZeroProb_mul_spin_eq_zero_of_flipInvariant E J m F hF,
    add_zero, vbg_exp_grahamZeroProb_eq_expJ]


theorem grahamAnchor_expJ_eq_zero_of_invariant
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (m : V)
    (F : ConfigSpace V -> Real)
    (hanchor : forall t, F (grahamPinConfig m t) = F t)
    (hflip : forall t, F (FieldGhostDict.flipV t) = F t) :
    expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) F =
      expJ E J (fun _ => 0) F := by
  rw [grahamAnchor_expJ_eq_pinned E J hdiag m F hanchor,
    vbg_exp_grahamPinnedProb_eq_of_flipInvariant E J m F hflip]


theorem grahamAnchor_fourPoint_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m i j k l : V}
    (him : i ≠ m) (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m)
        (fun t => (spin t i * spin t j) * (spin t k * spin t l)) =
      grahamFourPoint E J i j k l := by
  rw [grahamAnchor_expJ_eq_zero_of_invariant E J hdiag m]
  · exact (grahamFourPoint_eq_expJ E J i j k l).symm
  · intro t
    rw [spin_grahamPinConfig_of_ne m t him,
      spin_grahamPinConfig_of_ne m t hjm,
      spin_grahamPinConfig_of_ne m t hkm,
      spin_grahamPinConfig_of_ne m t hlm]
  · intro t
    simp only [FieldGhostDict.spin_flipV]
    ring


end StatMech.FrontierA
