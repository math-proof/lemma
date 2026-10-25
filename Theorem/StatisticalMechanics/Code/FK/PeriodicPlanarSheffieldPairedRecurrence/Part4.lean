/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem AlignedExactExtentPairedMixedBoundaryScores.wideSpan_formula
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k extentX extentY : Nat}
    (data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY) :
    data.raw.wideRightInt - data.raw.wideLeftInt =
      pairedWideSpanAtExtentX E Edual family familyDual schedule k extentX := by
  rw [data.wideRight_formula, data.wideLeft_formula]
  rfl


theorem AlignedExactExtentPairedMixedBoundaryScores.dualLeftSource_transport
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k k' extentX extentY extentX' extentY' : Nat}
    (old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k' extentX' extentY') :
    new.raw.data.dualLeftSource =
      old.raw.data.dualLeftSource.image (Pdual.shift
        (horizontalShift ((schedule.horizontal k' : Int) -
          schedule.horizontal k) +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k))) := by
  classical
  let delta : Int := (schedule.horizontal k' : Int) -
    schedule.horizontal k
  have hbase : new.raw.data.baseDual =
      old.raw.data.baseDual + horizontalShift delta +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k) := by
    funext i
    fin_cases i
    · change new.raw.data.baseDual 0 =
        (old.raw.data.baseDual + horizontalShift delta +
          verticalShift ((schedule.vertical k' : Int) -
            schedule.vertical k)) 0
      rw [new.dualBaseX_eq]
      simp only [Pi.add_apply, horizontalShift, verticalShift, delta]
      rw [old.dualBaseX_eq]
      norm_num
    · change new.raw.data.baseDual 1 =
        (old.raw.data.baseDual + horizontalShift delta +
          verticalShift ((schedule.vertical k' : Int) -
            schedule.vertical k)) 1
      rw [new.dualBaseY_eq]
      simp only [Pi.add_apply, horizontalShift, verticalShift, delta]
      rw [old.dualBaseY_eq]
      norm_num
  simp only [PairedMixedBoundaryScores.dualLeftSource,
    Finset.image_image]
  apply Finset.image_congr
  intro u hu
  rw [hbase]
  simp only [Function.comp_apply]
  rw [<- Pdual.shift_add]
  apply congrArg (fun z => Pdual.shift z u)
  abel


theorem AlignedExactExtentPairedMixedBoundaryScores.dualRightSource_transport
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k k' extentX extentY extentX' extentY' : Nat}
    (old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k' extentX' extentY')
    (hExtentX : (extentX' : Int) = extentX +
      2 * ((schedule.horizontal k' : Int) - schedule.horizontal k)) :
    new.raw.data.dualRightSource =
      old.raw.data.dualRightSource.image (Pdual.shift
        (horizontalShift ((schedule.horizontal k' : Int) -
          schedule.horizontal k) +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k))) := by
  classical
  let deltaH : Int := (schedule.horizontal k' : Int) -
    schedule.horizontal k
  let deltaV : Int := (schedule.vertical k' : Int) -
    schedule.vertical k
  have hsite : new.raw.data.baseDual + preferenceGridSite
        (Fin.last new.raw.data.widthDual,
          (0 : Fin (new.raw.data.heightDual + 1))) =
      old.raw.data.baseDual + preferenceGridSite
        (Fin.last old.raw.data.widthDual,
          (0 : Fin (old.raw.data.heightDual + 1))) +
        horizontalShift deltaH + verticalShift deltaV := by
    funext i
    fin_cases i
    · simp only [Pi.add_apply, preferenceGridSite,
        horizontalShift, verticalShift]
      norm_num
      rw [new.dualEndX_eq, old.dualEndX_eq]
      dsimp only [deltaH] at hExtentX ⊢
      omega
    · simp only [Pi.add_apply, preferenceGridSite,
        horizontalShift, verticalShift]
      norm_num
      rw [new.dualBaseY_eq, old.dualBaseY_eq]
      dsimp only [deltaV]
      omega
  simp only [PairedMixedBoundaryScores.dualRightSource,
    Finset.image_image]
  apply Finset.image_congr
  intro u hu
  rw [hsite]
  simp only [Function.comp_apply]
  rw [<- Pdual.shift_add]
  apply congrArg (fun z => Pdual.shift z u)
  abel


theorem AlignedExactExtentPairedMixedBoundaryScores.dualBottomSource_transport
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k k' extentX extentY extentX' extentY' : Nat}
    (old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k' extentX' extentY') :
    new.raw.data.dualBottomSource =
      old.raw.data.dualBottomSource.image (Pdual.shift
        (horizontalShift ((schedule.horizontal k' : Int) -
          schedule.horizontal k) +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k))) := by
  simpa only [PairedMixedBoundaryScores.dualBottomSource,
    PairedMixedBoundaryScores.dualLeftSource] using
      old.dualLeftSource_transport new


theorem AlignedExactExtentPairedMixedBoundaryScores.dualTopSource_transport
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k k' extentX extentY extentX' extentY' : Nat}
    (old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k' extentX' extentY')
    (hExtentY : (extentY' : Int) = extentY +
      2 * ((schedule.vertical k' : Int) - schedule.vertical k)) :
    new.raw.data.dualTopSource =
      old.raw.data.dualTopSource.image (Pdual.shift
        (horizontalShift ((schedule.horizontal k' : Int) -
          schedule.horizontal k) +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k))) := by
  classical
  let deltaH : Int := (schedule.horizontal k' : Int) -
    schedule.horizontal k
  let deltaV : Int := (schedule.vertical k' : Int) -
    schedule.vertical k
  have hsite : new.raw.data.baseDual + preferenceGridSite
        ((0 : Fin (new.raw.data.widthDual + 1)),
          Fin.last new.raw.data.heightDual) =
      old.raw.data.baseDual + preferenceGridSite
        ((0 : Fin (old.raw.data.widthDual + 1)),
          Fin.last old.raw.data.heightDual) +
        horizontalShift deltaH + verticalShift deltaV := by
    funext i
    fin_cases i
    · simp only [Pi.add_apply, preferenceGridSite,
        horizontalShift, verticalShift]
      norm_num
      rw [new.dualBaseX_eq, old.dualBaseX_eq]
      dsimp only [deltaH]
      omega
    · simp only [Pi.add_apply, preferenceGridSite,
        horizontalShift, verticalShift]
      norm_num
      rw [new.dualEndY_eq, old.dualEndY_eq]
      dsimp only [deltaV] at hExtentY ⊢
      omega
  simp only [PairedMixedBoundaryScores.dualTopSource,
    Finset.image_image]
  apply Finset.image_congr
  intro u hu
  rw [hsite]
  simp only [Function.comp_apply]
  rw [<- Pdual.shift_add]
  apply congrArg (fun z => Pdual.shift z u)
  abel


theorem AlignedExactExtentPairedMixedBoundaryScores.dualVerticalMerge_transport_measureReal_le
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    (hTI : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k k' extentX extentY extentX' extentY' radius : Nat}
    (old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k' extentX' extentY')
    (hExtentY : (extentY' : Int) = extentY +
      2 * ((schedule.vertical k' : Int) - schedule.vertical k))
    (hbox : Pdual.shift
      (horizontalShift ((schedule.horizontal k' : Int) -
          schedule.horizontal k) +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k)) ''
        (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <=
      Edual.rectVertices new.raw.data.wideLeft
        new.raw.data.wideRight 0 extentY') :
    muDual.real (Edual.rectanglePairMergeErrorUnion
        new.raw.data.wideLeft new.raw.data.wideRight 0 extentY'
        new.raw.data.dualBottomSource new.raw.data.dualTopSource) <=
      muDual.real (Pdual.pairMergeErrorUnion
        old.raw.data.dualBottomSource old.raw.data.dualTopSource radius) := by
  let z : Site 2 :=
    horizontalShift ((schedule.horizontal k' : Int) -
        schedule.horizontal k) +
      verticalShift ((schedule.vertical k' : Int) - schedule.vertical k)
  have hbound := old.raw.dualVerticalMerge_translate_measureReal_le
    hTI z new.raw.data.wideLeft new.raw.data.wideRight 0 extentY'
      radius hbox
  rw [old.dualBottomSource_transport new,
    old.dualTopSource_transport new hExtentY]
  simpa only [z] using hbound


theorem AlignedExactExtentPairedMixedBoundaryScores.dualHorizontalMerge_transport_measureReal_le
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    (hTI : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k k' extentX extentY extentX' extentY' radius : Nat}
    (old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k' extentX' extentY')
    (hExtentX : (extentX' : Int) = extentX +
      2 * ((schedule.horizontal k' : Int) - schedule.horizontal k))
    (hbox : Pdual.shift
      (horizontalShift ((schedule.horizontal k' : Int) -
          schedule.horizontal k) +
        verticalShift ((schedule.vertical k' : Int) -
          schedule.vertical k)) ''
        (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <=
      Edual.rectVertices 0 extentX' 0 extentY') :
    muDual.real (Edual.rectanglePairMergeErrorUnion 0 extentX' 0 extentY'
        new.raw.data.dualLeftSource new.raw.data.dualRightSource) <=
      muDual.real (Pdual.pairMergeErrorUnion
        old.raw.data.dualLeftSource old.raw.data.dualRightSource radius) := by
  let z : Site 2 :=
    horizontalShift ((schedule.horizontal k' : Int) -
        schedule.horizontal k) +
      verticalShift ((schedule.vertical k' : Int) - schedule.vertical k)
  have hbound := old.raw.dualHorizontalMerge_translate_measureReal_le
    hTI z 0 extentX' 0 extentY' radius hbox
  rw [old.dualLeftSource_transport new,
    old.dualRightSource_transport new hExtentX]
  simpa only [z] using hbound


end StatMech.FK.PeriodicPlanar
