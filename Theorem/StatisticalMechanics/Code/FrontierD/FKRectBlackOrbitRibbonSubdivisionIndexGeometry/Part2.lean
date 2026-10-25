/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeInjective
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectListFlatMapReplicate
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionIndexGeometry.Part2


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectBlackOrbitRibbonSubdivisionIndexEquiv_symm_val
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z : FKRectBlackOrbitRibbonSubdivisionIndex R omega d) :
    ((fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d).symm z).val =
      (finSigmaFinEquiv z).val := by
  rfl

theorem fkRectBlackOrbitRibbonSubdivisionIndexEquiv_symm_val_cast
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (scale : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length → ℕ)
    (hscale : scale = fun i =>
      onsAnisotropicStepScale (8 * R.medialTorus.width)
        (8 * R.medialTorus.height)
        (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i))
    (i : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length)
    (r : Fin (onsAnisotropicStepScale (8 * R.medialTorus.width)
      (8 * R.medialTorus.height)
      (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i))) :
    let r0 : Fin (scale i) := Fin.cast (congrFun hscale i).symm r
    ((fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d).symm ⟨i, r⟩).val =
      (finSigmaFinEquiv
        (⟨i, r0⟩ : Σ j, Fin (scale j))).val := by
  subst scale
  exact fkRectBlackOrbitRibbonSubdivisionIndexEquiv_symm_val
    R omega d ⟨i, r⟩

theorem fkRectBlackOrbitRibbonSubdivisionStepScale_pos
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length) :
    0 < onsAnisotropicStepScale (8 * R.medialTorus.width)
      (8 * R.medialTorus.height)
      (fkRectBlackOrbitMedialRibbonFlatDirection R omega d k) := by
  rcases fkRectFinFour_cases
      (fkRectBlackOrbitMedialRibbonFlatDirection R omega d k) with
    h | h | h | h <;>
    simp [onsAnisotropicStepScale, h, R.medialTorus.width_pos,
      R.medialTorus.height_pos]

set_option maxHeartbeats 1000000 in

theorem fkRectBlackOrbitRibbonSubdivisionDirection_nonUturn_index
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z : FKRectBlackOrbitRibbonSubdivisionIndex R omega d) :
    fkRectBlackOrbitMedialRibbonFlatDirection R omega d
        (fkRectFinSigmaSucc
          (fun i => onsAnisotropicStepScale (8 * R.medialTorus.width)
            (8 * R.medialTorus.height)
            (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i))
          (fkRectBlackOrbitRibbonSubdivisionStepScale_pos R omega d) z).1 ≠
      fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1 + 2 := by
  rcases z with ⟨i, r⟩
  simp only [fkRectFinSigmaSucc]
  split_ifs
  · intro h
    rcases fkRectFinFour_cases
        (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i) with
      hdir | hdir | hdir | hdir <;> simp [hdir] at h
  · exact fkRectBlackOrbitMedialRibbonFlatDirection_nonUturn R omega d i

set_option maxHeartbeats 500000 in

theorem fkRectBlackOrbitRibbonSubdivisionIndexEquiv_add_one
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (k : Fin (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length) :
    fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d (k + 1) =
      fkRectFinSigmaSucc
        (fun i => onsAnisotropicStepScale (8 * R.medialTorus.width)
          (8 * R.medialTorus.height)
          (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i))
        (fkRectBlackOrbitRibbonSubdivisionStepScale_pos R omega d)
        (fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d k) := by
  let scale := fun i => onsAnisotropicStepScale (8 * R.medialTorus.width)
    (8 * R.medialTorus.height)
    (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i)
  letI : NeZero (∑ i, scale i) := ⟨by
    rw [← fkRectBlackOrbitRibbonSubdivisionWord_length_eq_sum R omega d]
    exact NeZero.ne _⟩
  apply finSigmaFinEquiv.injective
  rw [finSigmaFinEquiv_fkRectFinSigmaSucc]
  simp only [fkRectBlackOrbitRibbonSubdivisionIndexEquiv,
    Equiv.trans_apply, Equiv.apply_symm_apply]
  exact finCongr_add_one
    (fkRectBlackOrbitRibbonSubdivisionWord_length_eq_sum R omega d) k


theorem fkRectBlackOrbitRibbonSubdivisionSide_eq_refinedProduct
    (R : FKRectTorus) :
    (8 * R.medialTorus.width) * (8 * R.medialTorus.height) =
      fkRectBlackOrbitRibbonSubdivisionSide R := by
  unfold fkRectBlackOrbitRibbonSubdivisionSide
  change (8 * (2 * R.width)) * (8 * R.height) =
    (16 * R.width) * (8 * R.height)
  ring

end
end StatMech.FrontierD
