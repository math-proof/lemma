/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part8


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectBlackOrbitSubdivisionSide_gt_two (R : FKRectTorus) :
    2 < fkRectBlackOrbitSubdivisionSide R := by
  unfold fkRectBlackOrbitSubdivisionSide
  nlinarith [R.width_pos, R.height_pos]


theorem fkRectBlackOrbitSubdivisionDart_valid
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    ∀ k,
      (fkRectBlackOrbitSubdivisionDart R omega d k).1 =
        ons_dirStep (fkRectBlackOrbitSubdivisionSide R)
          (fkRectBlackOrbitSubdivisionDart R omega d (k + 1)).2
          (fkRectBlackOrbitSubdivisionDart R omega d (k + 1)).1 := by
  let word := fkRectBlackOrbitShearSubdivisionWord R omega d
  have hword : word ≠ [] :=
    fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d
  letI : NeZero word.length :=
    ⟨(List.length_pos_iff_ne_nil.mpr hword).ne'⟩
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hw := fkRectBlackOrbitShearSubdivisionWord_preserves_winding R omega d
  have hdisp : (word.map stepOf).sum =
      ((fkRectBlackOrbitSubdivisionSide R : ℤ) * w.1,
        (fkRectBlackOrbitSubdivisionSide R : ℤ) * w.2) := by
    apply Prod.ext
    · rw [onsDirectionWord_stepOf_fst_sum]
      exact hw.1
    · rw [onsDirectionWord_stepOf_snd_sum]
      exact hw.2
  simpa only [fkRectBlackOrbitSubdivisionDart, word] using
    (onsDirectionWordTorusDart_valid
      (fkRectBlackOrbitSubdivisionSide R) word w.1 w.2 hdisp)


theorem fkRectBlackOrbitSubdivisionDart_nonUturn
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    ∀ k,
      (fkRectBlackOrbitSubdivisionDart R omega d k).2 ≠
        (fkRectBlackOrbitSubdivisionDart R omega d (k + 1)).2 + 2 := by
  let word := fkRectBlackOrbitShearSubdivisionWord R omega d
  have hword : word ≠ [] :=
    fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d
  letI : NeZero word.length :=
    ⟨(List.length_pos_iff_ne_nil.mpr hword).ne'⟩
  have hcyclic :=
    fkRectBlackOrbitShearSubdivisionWord_cyclicNonUturn R omega d
  simpa only [fkRectBlackOrbitSubdivisionDart, word] using
    (onsDirectionWordTorusDart_nonUturn
      (fkRectBlackOrbitSubdivisionSide R) word hcyclic)

theorem fkRectBlackOrbitSubdivisionDart_exponentX_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    (∑ k, ons_dirExponentX
      (fkRectBlackOrbitSubdivisionDart R omega d k).2) =
        (fkRectBlackOrbitSubdivisionSide R : ℤ) * w.1 := by
  dsimp only
  let word := fkRectBlackOrbitShearSubdivisionWord R omega d
  have hword : word ≠ [] :=
    fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d
  letI : NeZero word.length :=
    ⟨(List.length_pos_iff_ne_nil.mpr hword).ne'⟩
  rw [show (∑ k, ons_dirExponentX
      (fkRectBlackOrbitSubdivisionDart R omega d k).2) =
      (word.map ons_dirExponentX).sum by
        simpa only [fkRectBlackOrbitSubdivisionDart, word] using
          (onsDirectionWordTorusDart_exponentX_sum
            (fkRectBlackOrbitSubdivisionSide R) word)]
  exact (fkRectBlackOrbitShearSubdivisionWord_preserves_winding
    R omega d).1

theorem fkRectBlackOrbitSubdivisionDart_exponentY_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    (∑ k, ons_dirExponentY
      (fkRectBlackOrbitSubdivisionDart R omega d k).2) =
        (fkRectBlackOrbitSubdivisionSide R : ℤ) * w.2 := by
  dsimp only
  let word := fkRectBlackOrbitShearSubdivisionWord R omega d
  have hword : word ≠ [] :=
    fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d
  letI : NeZero word.length :=
    ⟨(List.length_pos_iff_ne_nil.mpr hword).ne'⟩
  rw [show (∑ k, ons_dirExponentY
      (fkRectBlackOrbitSubdivisionDart R omega d k).2) =
      (word.map ons_dirExponentY).sum by
        simpa only [fkRectBlackOrbitSubdivisionDart, word] using
          (onsDirectionWordTorusDart_exponentY_sum
            (fkRectBlackOrbitSubdivisionSide R) word)]
  exact (fkRectBlackOrbitShearSubdivisionWord_preserves_winding
    R omega d).2


theorem fkRectBlackBoundaryPrimalCycleWinding_fst_odd_of_site_injective
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hsite : Function.Injective (fun k ↦
      (fkRectBlackOrbitSubdivisionDart R omega d k).1))
    (hy : (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0)
    (hx : (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 ≠ 0) :
    Odd (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 := by
  letI : Fact (2 < fkRectBlackOrbitSubdivisionSide R) :=
    ⟨fkRectBlackOrbitSubdivisionSide_gt_two R⟩
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  apply ons_simpleLoop_horizontal_winding_odd_of_ne_zero
    (fkRectBlackOrbitSubdivisionDart R omega d)
    (fkRectBlackOrbitSubdivisionDart_valid R omega d)
    hsite
    (fkRectBlackOrbitSubdivisionDart_nonUturn R omega d)
    w.1
    (fkRectBlackOrbitSubdivisionDart_exponentX_sum R omega d)
  · rw [fkRectBlackOrbitSubdivisionDart_exponentY_sum]
    simp [w, hy]
  · exact hx

end
end StatMech.FrontierD
