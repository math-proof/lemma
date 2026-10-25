/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem exists_pairedAlignedConnectorSlack
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (radius : Nat) : exists k,
    PairedAlignedConnectorSlack E Edual family familyDual schedule radius k := by
  let ML : Int := E.connectorMarginRequirement radius
  let MD : Int := Edual.connectorMarginRequirement radius
  let h1 : Int := ML - family.baseLeft 0
  let h2 : Int := family.baseRight 0 + ML
  let h3 : Int := MD - familyDual.baseLeft 0
  let h4 : Int := familyDual.baseRight 0 + MD
  let v1 : Int := ML - family.baseBottom 1
  let v2 : Int := family.baseTop 1 + ML
  let v3 : Int := MD - familyDual.baseBottom 1
  let v4 : Int := familyDual.baseTop 1 + MD
  let horizontalTarget := h1.natAbs + h2.natAbs + h3.natAbs + h4.natAbs
  let verticalTarget := v1.natAbs + v2.natAbs + v3.natAbs + v4.natAbs
  have hHorizontal : ∀ᶠ eventuallyK in atTop,
      horizontalTarget <= schedule.horizontal eventuallyK :=
    schedule.horizontal_tendsto (eventually_ge_atTop horizontalTarget)
  have hVertical : ∀ᶠ eventuallyK in atTop,
      verticalTarget <= schedule.vertical eventuallyK :=
    schedule.vertical_tendsto (eventually_ge_atTop verticalTarget)
  obtain ⟨horizontalIndex, hHorizontalIndex⟩ :=
    eventually_atTop.1 hHorizontal
  obtain ⟨verticalIndex, hVerticalIndex⟩ :=
    eventually_atTop.1 hVertical
  let k := max horizontalIndex verticalIndex
  have hkH := hHorizontalIndex k (Nat.le_max_left _ _)
  have hkV := hVerticalIndex k (Nat.le_max_right _ _)
  have hh1 : h1 <= (schedule.horizontal k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show h1.natAbs <= schedule.horizontal k by
      apply (show h1.natAbs <= horizontalTarget by
        dsimp [horizontalTarget]; omega) |>.trans hkH)
  have hh2 : h2 <= (schedule.horizontal k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show h2.natAbs <= schedule.horizontal k by
      apply (show h2.natAbs <= horizontalTarget by
        dsimp [horizontalTarget]; omega) |>.trans hkH)
  have hh3 : h3 <= (schedule.horizontal k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show h3.natAbs <= schedule.horizontal k by
      apply (show h3.natAbs <= horizontalTarget by
        dsimp [horizontalTarget]; omega) |>.trans hkH)
  have hh4 : h4 <= (schedule.horizontal k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show h4.natAbs <= schedule.horizontal k by
      apply (show h4.natAbs <= horizontalTarget by
        dsimp [horizontalTarget]; omega) |>.trans hkH)
  have hv1 : v1 <= (schedule.vertical k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show v1.natAbs <= schedule.vertical k by
      apply (show v1.natAbs <= verticalTarget by
        dsimp [verticalTarget]; omega) |>.trans hkV)
  have hv2 : v2 <= (schedule.vertical k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show v2.natAbs <= schedule.vertical k by
      apply (show v2.natAbs <= verticalTarget by
        dsimp [verticalTarget]; omega) |>.trans hkV)
  have hv3 : v3 <= (schedule.vertical k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show v3.natAbs <= schedule.vertical k by
      apply (show v3.natAbs <= verticalTarget by
        dsimp [verticalTarget]; omega) |>.trans hkV)
  have hv4 : v4 <= (schedule.vertical k : Int) := by
    apply Int.le_natAbs.trans
    exact_mod_cast (show v4.natAbs <= schedule.vertical k by
      apply (show v4.natAbs <= verticalTarget by
        dsimp [verticalTarget]; omega) |>.trans hkV)
  refine ⟨k, ?_⟩
  constructor <;> dsimp only [h1, h2, h3, h4, v1, v2, v3, v4, ML, MD]
    at hh1 hh2 hh3 hh4 hv1 hv2 hv3 hv4 ⊢ <;> omega


theorem AlignedExactExtentPairedMixedBoundaryScores.primalConnector_subset_narrow
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k extentX extentY radius : Nat}
    (data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (slack : PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius k) :
    forall v : PreferenceGridVertex data.raw.data.width data.raw.data.height,
      P.shift (data.raw.data.base + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
        E.rectVertices 0 extentX 0 extentY := by
  apply data.raw.primalConnector_subset_narrow
  · simpa [data.primalBaseX_eq] using slack.primalLeft
  · rw [data.primalEndX_eq]
    have := slack.primalRight
    omega
  · simpa [data.primalBaseY_eq] using slack.primalBottom
  · rw [data.primalEndY_eq]
    have := slack.primalTop
    omega


theorem AlignedExactExtentPairedMixedBoundaryScores.dualConnector_subset_narrow
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k extentX extentY radius : Nat}
    (data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (slack : PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius k) :
    forall v : PreferenceGridVertex
      data.raw.data.widthDual data.raw.data.heightDual,
      Pdual.shift (data.raw.data.baseDual + preferenceGridSite v) ''
          (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) ⊆
        Edual.rectVertices 0 extentX 0 extentY := by
  apply data.raw.dualConnector_subset_narrow
  · simpa [data.dualBaseX_eq] using slack.dualLeft
  · rw [data.dualEndX_eq]
    have := slack.dualRight
    omega
  · simpa [data.dualBaseY_eq] using slack.dualBottom
  · rw [data.dualEndY_eq]
    have := slack.dualTop
    omega


theorem AlignedExactExtentPairedMixedBoundaryScores.primalConnector_subset_wide
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k extentX extentY radius : Nat}
    (data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (slack : PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius k) :
    forall v : PreferenceGridVertex data.raw.data.width data.raw.data.height,
      P.shift (data.raw.data.base + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
        E.rectVertices data.raw.data.wideLeft data.raw.data.wideRight
          0 data.raw.data.shortTop := by
  intro gridVertex
  apply (data.primalConnector_subset_narrow slack gridVertex).trans
  apply E.rectVertices_mono
  · exact data.raw.data.wideLeft_le
  · simpa [data.raw.narrowRight_eq] using data.raw.data.narrowRight_le
  · exact le_rfl
  · rw [data.raw.shortTop_eq]


theorem AlignedExactExtentPairedMixedBoundaryScores.dualConnector_subset_wide
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k extentX extentY radius : Nat}
    (data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY)
    (slack : PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius k) :
    forall v : PreferenceGridVertex
      data.raw.data.widthDual data.raw.data.heightDual,
      Pdual.shift (data.raw.data.baseDual + preferenceGridSite v) ''
          (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) ⊆
        Edual.rectVertices data.raw.data.wideLeft data.raw.data.wideRight
          0 data.raw.data.shortTop := by
  intro gridVertex
  apply (data.dualConnector_subset_narrow slack gridVertex).trans
  apply Edual.rectVertices_mono
  · exact data.raw.data.wideLeft_le
  · simpa [data.raw.narrowRight_eq] using data.raw.data.narrowRight_le
  · exact le_rfl
  · rw [data.raw.shortTop_eq]


theorem exists_alignedExactExtentPairedMixedBoundaryScores_atExtents
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k extentX extentY : Nat)
    (hposX : 0 < family.baseRight 0 - schedule.horizontal k + extentX -
      (family.baseLeft 0 + schedule.horizontal k))
    (hposXDual : 0 < familyDual.baseRight 0 - schedule.horizontal k +
      extentX - (familyDual.baseLeft 0 + schedule.horizontal k))
    (hposY : 0 < family.baseTop 1 - schedule.vertical k + extentY -
      (family.baseBottom 1 + schedule.vertical k))
    (hposYDual : 0 < familyDual.baseTop 1 - schedule.vertical k +
      extentY - (familyDual.baseBottom 1 + schedule.vertical k))
    (hleftP : family.radiusLeft (schedule.horizontal k) <= extentX)
    (hrightP : family.radiusRight (schedule.horizontal k) <= extentX)
    (hbottomP : family.radiusBottom (schedule.vertical k) <= extentY)
    (htopP : family.radiusTop (schedule.vertical k) <= extentY)
    (hleftD : familyDual.radiusLeft (schedule.horizontal k) <= extentX)
    (hrightD : familyDual.radiusRight (schedule.horizontal k) <= extentX)
    (hbottomD : familyDual.radiusBottom (schedule.vertical k) <= extentY)
    (htopD : familyDual.radiusTop (schedule.vertical k) <= extentY) :
    Nonempty (AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual family familyDual schedule k extentX extentY) := by
  let h := schedule.horizontal k
  let v := schedule.vertical k
  let left : Site 2 := family.baseLeft + horizontalShift h
  let right : Site 2 := family.baseRight + horizontalShift (-(h : Int))
  let bottom : Site 2 := family.baseBottom + verticalShift v
  let top : Site 2 := family.baseTop + verticalShift (-(v : Int))
  let leftDual : Site 2 := familyDual.baseLeft + horizontalShift h
  let rightDual : Site 2 :=
    familyDual.baseRight + horizontalShift (-(h : Int))
  let bottomDual : Site 2 := familyDual.baseBottom + verticalShift v
  let topDual : Site 2 := familyDual.baseTop + verticalShift (-(v : Int))
  let width := boundaryGridWidth extentX left right
  let height := boundaryGridHeight extentY bottom top
  let widthDual := boundaryGridWidth extentX leftDual rightDual
  let heightDual := boundaryGridHeight extentY bottomDual topDual
  have hx0 : 0 < right 0 + (extentX : Int) - left 0 := by
    simpa [left, right, h] using hposX
  have hxDual0 : 0 < rightDual 0 + (extentX : Int) - leftDual 0 := by
    simpa [leftDual, rightDual, h] using hposXDual
  have hy0 : 0 < top 1 + (extentY : Int) - bottom 1 := by
    simpa [bottom, top, v] using hposY
  have hyDual0 : 0 < topDual 1 + (extentY : Int) - bottomDual 1 := by
    simpa [bottomDual, topDual, v] using hposYDual
  have hwidth : 0 < width := boundaryGridWidth_pos _ _ _ hx0
  have hheight : 0 < height := boundaryGridHeight_pos _ _ _ hy0
  have hwidthDual : 0 < widthDual :=
    boundaryGridWidth_pos _ _ _ hxDual0
  have hheightDual : 0 < heightDual :=
    boundaryGridHeight_pos _ _ _ hyDual0
  have hb : (family.baseLeft 0 + h + width -
      (family.baseRight 0 - h) : Int) = extentX := by
    have hnonneg : 0 <= right 0 + (extentX : Int) - left 0 := hx0.le
    have hwidthCast : (width : Int) = right 0 + extentX - left 0 := by
      dsimp only [width, boundaryGridWidth]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hwidthCast]
    simp [left, right]
    omega
  have hbDual : (familyDual.baseLeft 0 + h + widthDual -
      (familyDual.baseRight 0 - h) : Int) = extentX := by
    have hnonneg : 0 <= rightDual 0 + (extentX : Int) - leftDual 0 :=
      hxDual0.le
    have hwidthCast :
        (widthDual : Int) = rightDual 0 + extentX - leftDual 0 := by
      dsimp only [widthDual, boundaryGridWidth]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hwidthCast]
    simp [leftDual, rightDual]
    omega
  have hd : (family.baseBottom 1 + v + height -
      (family.baseTop 1 - v) : Int) = extentY := by
    have hnonneg : 0 <= top 1 + (extentY : Int) - bottom 1 := hy0.le
    have hheightCast : (height : Int) = top 1 + extentY - bottom 1 := by
      dsimp only [height, boundaryGridHeight]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hheightCast]
    simp [bottom, top]
    omega
  have hdDual : (familyDual.baseBottom 1 + v + heightDual -
      (familyDual.baseTop 1 - v) : Int) = extentY := by
    have hnonneg :
        0 <= topDual 1 + (extentY : Int) - bottomDual 1 := hyDual0.le
    have hheightCast :
        (heightDual : Int) = topDual 1 + extentY - bottomDual 1 := by
      dsimp only [heightDual, boundaryGridHeight]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hheightCast]
    simp [bottomDual, topDual]
    omega
  let base : Site 2 := fun i => if i = 0 then
    family.baseLeft 0 + h else family.baseBottom 1 + v
  let baseDual : Site 2 := fun i => if i = 0 then
    familyDual.baseLeft 0 + h else familyDual.baseBottom 1 + v
  let bottomLower : Int := base 0 - family.baseBottom 0 -
    family.radiusBottom v
  let topLower : Int := base 0 - family.baseTop 0 - family.radiusTop v
  let aP : Int := min 0 (min bottomLower topLower)
  let bottomUpper : Int := base 0 + width - family.baseBottom 0 +
    family.radiusBottom v
  let topUpper : Int := base 0 + width - family.baseTop 0 +
    family.radiusTop v
  let bP : Int := max extentX (max bottomUpper topUpper)
  let leftUpper : Int := base 1 + height - family.baseLeft 1 +
    family.radiusLeft h
  let rightUpper : Int := base 1 + height - family.baseRight 1 +
    family.radiusRight h
  let dP : Int := max extentY (max leftUpper rightUpper)
  let bottomLowerDual : Int := baseDual 0 - familyDual.baseBottom 0 -
    familyDual.radiusBottom v
  let topLowerDual : Int :=
    baseDual 0 - familyDual.baseTop 0 - familyDual.radiusTop v
  let aD : Int := min 0 (min bottomLowerDual topLowerDual)
  let bottomUpperDual : Int := baseDual 0 + widthDual -
    familyDual.baseBottom 0 + familyDual.radiusBottom v
  let topUpperDual : Int := baseDual 0 + widthDual -
    familyDual.baseTop 0 + familyDual.radiusTop v
  let bD : Int := max extentX (max bottomUpperDual topUpperDual)
  let leftUpperDual : Int := baseDual 1 + heightDual -
    familyDual.baseLeft 1 + familyDual.radiusLeft h
  let rightUpperDual : Int := baseDual 1 + heightDual -
    familyDual.baseRight 1 + familyDual.radiusRight h
  let dD : Int := max extentY (max leftUpperDual rightUpperDual)
  let a := min aP aD
  let b := max bP bD
  let d := max dP dD
  have hmixedP := family.mixedBoundaryScores E mu hTI h v width height
    (schedule.primal_left_bottom k) (schedule.primal_right_bottom k)
    (by simpa [base, hb, h] using (show (family.radiusLeft h : Int) <=
      extentX by exact_mod_cast hleftP))
    (by simpa [base, hb, h] using (show (family.radiusRight h : Int) <=
      extentX by exact_mod_cast hrightP))
    (by simpa [base, hd, v] using (show (family.radiusBottom v : Int) <=
      extentY by exact_mod_cast hbottomP))
    (by simpa [base, hd, v] using (show (family.radiusTop v : Int) <=
      extentY by exact_mod_cast htopP))
  have hmixedD := familyDual.mixedBoundaryScores Edual muDual hTIDual
    h v widthDual heightDual (schedule.dual_left_bottom k)
    (schedule.dual_right_bottom k)
    (by simpa [baseDual, hbDual, h] using
      (show (familyDual.radiusLeft h : Int) <= extentX by
        exact_mod_cast hleftD))
    (by simpa [baseDual, hbDual, h] using
      (show (familyDual.radiusRight h : Int) <= extentX by
        exact_mod_cast hrightD))
    (by simpa [baseDual, hdDual, v] using
      (show (familyDual.radiusBottom v : Int) <= extentY by
        exact_mod_cast hbottomD))
    (by simpa [baseDual, hdDual, v] using
      (show (familyDual.radiusTop v : Int) <= extentY by
        exact_mod_cast htopD))
  dsimp only at hmixedP hmixedD
  simp only [if_pos (rfl : (0 : Fin 2) = 0),
    if_neg (by decide : (1 : Fin 2) ≠ 0), if_true, if_false]
      at hmixedP hmixedD
  rw [hb, hd] at hmixedP
  rw [hbDual, hdDual] at hmixedD
  change (((aP : Real) <= 0 /\ (extentX : Real) <= bP /\
      (0 : Real) <= 0 /\ (extentY : Real) <= dP) /\ _) at hmixedP
  change (((aD : Real) <= 0 /\ (extentX : Real) <= bD /\
      (0 : Real) <= 0 /\ (extentY : Real) <= dD) /\ _) at hmixedD
  have hdP : dP = extentY := by
    have hleft := schedule.primal_left_top k
    have hright := schedule.primal_right_top k
    change (family.radiusLeft h : Int) + family.baseTop 1 <=
      family.baseLeft 1 + v at hleft
    change (family.radiusRight h : Int) + family.baseTop 1 <=
      family.baseRight 1 + v at hright
    have hbaseHeight : family.baseBottom 1 + (v : Int) + height =
        (extentY : Int) + family.baseTop 1 - v := by omega
    dsimp only [dP, leftUpper, rightUpper]
    simp only [base, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rw [hbaseHeight]
    omega
  have hdD : dD = extentY := by
    have hleft := schedule.dual_left_top k
    have hright := schedule.dual_right_top k
    change (familyDual.radiusLeft h : Int) + familyDual.baseTop 1 <=
      familyDual.baseLeft 1 + v at hleft
    change (familyDual.radiusRight h : Int) + familyDual.baseTop 1 <=
      familyDual.baseRight 1 + v at hright
    have hbaseHeight : familyDual.baseBottom 1 + (v : Int) + heightDual =
        (extentY : Int) + familyDual.baseTop 1 - v := by omega
    dsimp only [dD, leftUpperDual, rightUpperDual]
    simp only [baseDual, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rw [hbaseHeight]
    omega
  have hdCommon : d = extentY := by simp [d, hdP, hdD]
  let raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY := {
    data := {
    width := width
    height := height
    widthDual := widthDual
    heightDual := heightDual
    width_pos := hwidth
    height_pos := hheight
    widthDual_pos := hwidthDual
    heightDual_pos := hheightDual
    base := base
    baseDual := baseDual
    narrowRight := extentX
    shortTop := extentY
    wideLeft := a
    wideRight := b
    tallTop := d
    wideLeft_le := by
      exact (show (a : Real) <= (aP : Real) by
        exact_mod_cast min_le_left aP aD).trans hmixedP.1.1
    narrowRight_le := by
      exact hmixedP.1.2.1.trans (show (bP : Real) <= (b : Real) by
        exact_mod_cast le_max_left bP bD)
    shortTop_le := by
      exact hmixedP.1.2.2.2.trans (show (dP : Real) <= (d : Real) by
        exact_mod_cast le_max_left dP dD)
    primal_bottom := fun i => (hmixedP.2.1 i).trans_le (measureReal_mono
      (E.rectBottomConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_left aP aD)
        (by exact_mod_cast le_max_left bP bD) le_rfl))
    primal_top := fun i => (hmixedP.2.2.1 i).trans_le (measureReal_mono
      (E.rectTopConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_left aP aD)
        (by exact_mod_cast le_max_left bP bD) le_rfl))
    primal_left := fun j => (hmixedP.2.2.2.1 j).trans_le (measureReal_mono
      (E.rectLeftConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_left dP dD)))
    primal_right := fun j => (hmixedP.2.2.2.2 j).trans_le (measureReal_mono
      (E.rectRightConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_left dP dD)))
    dual_bottom := fun i => (hmixedD.2.1 i).trans_le (measureReal_mono
      (Edual.rectBottomConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_right aP aD)
        (by exact_mod_cast le_max_right bP bD) le_rfl))
    dual_top := fun i => (hmixedD.2.2.1 i).trans_le (measureReal_mono
      (Edual.rectTopConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_right aP aD)
        (by exact_mod_cast le_max_right bP bD) le_rfl))
    dual_left := fun j => (hmixedD.2.2.2.1 j).trans_le (measureReal_mono
      (Edual.rectLeftConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_right dP dD)))
    dual_right := fun j => (hmixedD.2.2.2.2 j).trans_le (measureReal_mono
      (Edual.rectRightConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_right dP dD))) }
    wideLeftInt := a
    wideRightInt := b
    narrowRight_eq := rfl
    shortTop_eq := rfl
    tallTop_eq := by
      change (d : Real) = (extentY : Real)
      exact_mod_cast hdCommon
    wideLeft_eq := rfl
    wideRight_eq := rfl }
  refine ⟨{
    raw := raw
    primalBaseX_eq := ?_
    primalEndX_eq := ?_
    primalBaseY_eq := ?_
    primalEndY_eq := ?_
    dualBaseX_eq := ?_
    dualEndX_eq := ?_
    dualBaseY_eq := ?_
    dualEndY_eq := ?_
    wideLeft_formula := ?_
    wideRight_formula := ?_ }⟩
  · simp [raw, base, h]
  · dsimp only [raw]
    simp only [base, if_pos (rfl : (0 : Fin 2) = 0)]
    omega
  · simp [raw, base, v]
  · dsimp only [raw]
    simp only [base, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    omega
  · simp [raw, baseDual, h]
  · dsimp only [raw]
    simp only [baseDual, if_pos (rfl : (0 : Fin 2) = 0)]
    omega
  · simp [raw, baseDual, v]
  · dsimp only [raw]
    simp only [baseDual, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    omega
  · simp [raw, pairedWideLeftAtExtentX, a, aP, aD, bottomLower,
      topLower, bottomLowerDual, topLowerDual, base, baseDual, h, v,
      left, right, leftDual, rightDual]
  · simp [raw, pairedWideRightAtExtentX, b, bP, bD, bottomUpper,
      topUpper, bottomUpperDual, topUpperDual, base, baseDual, h, v,
      left, right, leftDual, rightDual, width, widthDual]


theorem exists_pairedMixedBoundaryScores_atExtents
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k extentX extentY : Nat)
    (hposX : 0 < family.baseRight 0 - schedule.horizontal k + extentX -
      (family.baseLeft 0 + schedule.horizontal k))
    (hposXDual : 0 < familyDual.baseRight 0 - schedule.horizontal k +
      extentX - (familyDual.baseLeft 0 + schedule.horizontal k))
    (hposY : 0 < family.baseTop 1 - schedule.vertical k + extentY -
      (family.baseBottom 1 + schedule.vertical k))
    (hposYDual : 0 < familyDual.baseTop 1 - schedule.vertical k +
      extentY - (familyDual.baseBottom 1 + schedule.vertical k))
    (hleftP : family.radiusLeft (schedule.horizontal k) <= extentX)
    (hrightP : family.radiusRight (schedule.horizontal k) <= extentX)
    (hbottomP : family.radiusBottom (schedule.vertical k) <= extentY)
    (htopP : family.radiusTop (schedule.vertical k) <= extentY)
    (hleftD : familyDual.radiusLeft (schedule.horizontal k) <= extentX)
    (hrightD : familyDual.radiusRight (schedule.horizontal k) <= extentX)
    (hbottomD : familyDual.radiusBottom (schedule.vertical k) <= extentY)
    (htopD : familyDual.radiusTop (schedule.vertical k) <= extentY) :
    Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY) := by
  exact Nonempty.map AlignedExactExtentPairedMixedBoundaryScores.raw
    (exists_alignedExactExtentPairedMixedBoundaryScores_atExtents
      E Edual mu muDual hTI hTIDual family familyDual schedule k
      extentX extentY hposX hposXDual hposY hposYDual hleftP hrightP
      hbottomP htopP hleftD hrightD hbottomD htopD)


theorem exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k : Nat) :
    exists thresholdX thresholdY, forall {extentX extentY},
      thresholdX <= extentX -> thresholdY <= extentY ->
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
        S Sdual p pDual family familyDual schedule k extentX extentY) := by
  let h := schedule.horizontal k
  let v := schedule.vertical k
  let radiusX := max
    (max (family.radiusLeft h) (family.radiusRight h))
    (max (familyDual.radiusLeft h) (familyDual.radiusRight h))
  let radiusY := max
    (max (family.radiusBottom v) (family.radiusTop v))
    (max (familyDual.radiusBottom v) (familyDual.radiusTop v))
  let gapX : Int := family.baseLeft 0 + 2 * h - family.baseRight 0
  let gapXDual : Int :=
    familyDual.baseLeft 0 + 2 * h - familyDual.baseRight 0
  let gapY : Int := family.baseBottom 1 + 2 * v - family.baseTop 1
  let gapYDual : Int :=
    familyDual.baseBottom 1 + 2 * v - familyDual.baseTop 1
  let thresholdX := max radiusX
    (max (gapX.natAbs + 1) (gapXDual.natAbs + 1))
  let thresholdY := max radiusY
    (max (gapY.natAbs + 1) (gapYDual.natAbs + 1))
  refine ⟨thresholdX, thresholdY, ?_⟩
  intro extentX extentY hX hY
  have hradiusX : radiusX <= extentX :=
    (Nat.le_max_left _ _).trans hX
  have hradiusY : radiusY <= extentY :=
    (Nat.le_max_left _ _).trans hY
  have hgapX : gapX.natAbs + 1 <= extentX :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _) |>.trans hX
  have hgapXDual : gapXDual.natAbs + 1 <= extentX :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _) |>.trans hX
  have hgapY : gapY.natAbs + 1 <= extentY :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _) |>.trans hY
  have hgapYDual : gapYDual.natAbs + 1 <= extentY :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _) |>.trans hY
  have hposX : 0 < family.baseRight 0 - h + extentX -
      (family.baseLeft 0 + h) := by
    have hgap : gapX < (extentX : Int) := by
      have habs : gapX <= (gapX.natAbs : Int) := Int.le_natAbs
      have hcast : (gapX.natAbs + 1 : Int) <= extentX := by
        exact_mod_cast hgapX
      omega
    dsimp only [gapX] at hgap
    omega
  have hposXDual : 0 < familyDual.baseRight 0 - h + extentX -
      (familyDual.baseLeft 0 + h) := by
    have hgap : gapXDual < (extentX : Int) := by
      have habs : gapXDual <= (gapXDual.natAbs : Int) := Int.le_natAbs
      have hcast : (gapXDual.natAbs + 1 : Int) <= extentX := by
        exact_mod_cast hgapXDual
      omega
    dsimp only [gapXDual] at hgap
    omega
  have hposY : 0 < family.baseTop 1 - v + extentY -
      (family.baseBottom 1 + v) := by
    have hgap : gapY < (extentY : Int) := by
      have habs : gapY <= (gapY.natAbs : Int) := Int.le_natAbs
      have hcast : (gapY.natAbs + 1 : Int) <= extentY := by
        exact_mod_cast hgapY
      omega
    dsimp only [gapY] at hgap
    omega
  have hposYDual : 0 < familyDual.baseTop 1 - v + extentY -
      (familyDual.baseBottom 1 + v) := by
    have hgap : gapYDual < (extentY : Int) := by
      have habs : gapYDual <= (gapYDual.natAbs : Int) := Int.le_natAbs
      have hcast : (gapYDual.natAbs + 1 : Int) <= extentY := by
        exact_mod_cast hgapYDual
      omega
    dsimp only [gapYDual] at hgap
    omega
  exact exists_alignedExactExtentPairedMixedBoundaryScores_atExtents
    E Edual mu muDual
    hTI hTIDual family familyDual schedule k extentX extentY
    hposX hposXDual hposY hposYDual
    ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _) |>.trans hradiusX)
    ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _) |>.trans hradiusX)
    ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _) |>.trans hradiusY)
    ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _) |>.trans hradiusY)
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _) |>.trans hradiusX)
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _) |>.trans hradiusX)
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _) |>.trans hradiusY)
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _) |>.trans hradiusY)


theorem exists_exactExtentPairedMixedBoundaryScores_thresholds
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k : Nat) :
    exists thresholdX thresholdY, forall {extentX extentY},
      thresholdX <= extentX -> thresholdY <= extentY ->
      Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual
        S Sdual p pDual extentX extentY) := by
  obtain ⟨thresholdX, thresholdY, hthreshold⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  refine ⟨thresholdX, thresholdY, ?_⟩
  intro extentX extentY hX hY
  exact Nonempty.map AlignedExactExtentPairedMixedBoundaryScores.raw
    (hthreshold hX hY)


theorem ExactExtentPairedMixedBoundaryScores.extentX_le_wideSpan
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY) :
    (extentX : Int) <= raw.wideRightInt - raw.wideLeftInt := by
  have hleft : (raw.wideLeftInt : Real) <= 0 := by
    simpa [raw.wideLeft_eq] using raw.data.wideLeft_le
  have hright : (extentX : Real) <= raw.wideRightInt := by
    simpa [raw.narrowRight_eq, raw.wideRight_eq] using
      raw.data.narrowRight_le
  exact_mod_cast (show (extentX : Real) <=
    raw.wideRightInt - raw.wideLeftInt by linarith)


theorem ExactExtentPairedMixedBoundaryScores.dualVerticalMerge_translate_measureReal_le
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hTI : Pdual.IsTranslationInvariant muDual)
    (z : Site 2) (a b c d : Real) (radius : Nat)
    (hbox : Pdual.shift z ''
        (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <=
      Edual.rectVertices a b c d) :
    muDual.real (Edual.rectanglePairMergeErrorUnion a b c d
        (raw.data.dualBottomSource.image (Pdual.shift z))
        (raw.data.dualTopSource.image (Pdual.shift z))) <=
      muDual.real (Pdual.pairMergeErrorUnion
        raw.data.dualBottomSource raw.data.dualTopSource radius) := by
  exact Edual.translated_rectanglePairMergeErrorUnion_measureReal_le
    muDual hTI z a b c d raw.data.dualBottomSource
      raw.data.dualTopSource radius hbox


theorem ExactExtentPairedMixedBoundaryScores.dualHorizontalMerge_translate_measureReal_le
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hTI : Pdual.IsTranslationInvariant muDual)
    (z : Site 2) (a b c d : Real) (radius : Nat)
    (hbox : Pdual.shift z ''
        (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <=
      Edual.rectVertices a b c d) :
    muDual.real (Edual.rectanglePairMergeErrorUnion a b c d
        (raw.data.dualLeftSource.image (Pdual.shift z))
        (raw.data.dualRightSource.image (Pdual.shift z))) <=
      muDual.real (Pdual.pairMergeErrorUnion
        raw.data.dualLeftSource raw.data.dualRightSource radius) := by
  exact Edual.translated_rectanglePairMergeErrorUnion_measureReal_le
    muDual hTI z a b c d raw.data.dualLeftSource
      raw.data.dualRightSource radius hbox


theorem ExactExtentPairedMixedBoundaryScores.dualVerticalCrossing_ge_translate_inactive
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hTI : Pdual.IsTranslationInvariant muDual)
    (z : Site 2) (a b : Real) (radius : Nat)
    (ha : a <= raw.data.wideLeft + (z 0 : Real))
    (hb : raw.data.wideRight + (z 0 : Real) <= b)
    (hbox : Pdual.shift z ''
        (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <=
      Edual.rectVertices a b (z 1 : Real)
        ((extentY : Real) + (z 1 : Real))) :
    muDual.real (Edual.rectSideConnectionEvent
        raw.data.wideLeft raw.data.wideRight 0 extentY
        (raw.data.dualBottomSource : Set W)
        (Edual.rectBottomBoundaryVertices
          raw.data.wideLeft raw.data.wideRight 0 extentY)) *
      muDual.real (Edual.rectSideConnectionEvent
        raw.data.wideLeft raw.data.wideRight 0 extentY
        (raw.data.dualTopSource : Set W)
        (Edual.rectTopBoundaryVertices
          raw.data.wideLeft raw.data.wideRight 0 extentY)) -
      muDual.real (Pdual.pairMergeErrorUnion
        raw.data.dualBottomSource raw.data.dualTopSource radius) <=
      muDual.real (Edual.verticalCrossingEvent a b (z 1 : Real)
        ((extentY : Real) + (z 1 : Real))) := by
  let bottom := raw.data.dualBottomSource.image (Pdual.shift z)
  let top := raw.data.dualTopSource.image (Pdual.shift z)
  have hcarried := Edual.verticalCrossing_ge_carriedComponents
    muDual hFKG a b (z 1 : Real) ((extentY : Real) + (z 1 : Real))
    bottom top
    (raw.data.wideLeft + (z 0 : Real))
    (raw.data.wideRight + (z 0 : Real))
    ((extentY : Real) + (z 1 : Real))
    (raw.data.wideLeft + (z 0 : Real))
    (raw.data.wideRight + (z 0 : Real)) (z 1 : Real)
    a b (z 1 : Real) ((extentY : Real) + (z 1 : Real))
    ha hb le_rfl ha hb le_rfl le_rfl le_rfl le_rfl le_rfl
  have hmerge := raw.dualVerticalMerge_translate_measureReal_le
    hTI z a b (z 1 : Real) ((extentY : Real) + (z 1 : Real))
      radius hbox
  have hbottom := Edual.rectBottomConnection_translate_measureReal_eq
    muDual hTI z raw.data.wideLeft raw.data.wideRight 0 extentY
      (raw.data.dualBottomSource : Set W)
  have htop := Edual.rectTopConnection_translate_measureReal_eq
    muDual hTI z raw.data.wideLeft raw.data.wideRight 0 extentY
      (raw.data.dualTopSource : Set W)
  have hbottom' := hbottom
  have htop' := htop
  simp only [zero_add] at hbottom' htop'
  simp only [bottom, top, Finset.coe_image] at hcarried
  rw [hbottom', htop'] at hcarried
  linarith


theorem ExactExtentPairedMixedBoundaryScores.dualHorizontalCrossing_ge_translate_inactive
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hTI : Pdual.IsTranslationInvariant muDual)
    (z : Site 2) (c d : Real) (radius : Nat)
    (hc : c <= (z 1 : Real))
    (hd : (extentY : Real) + (z 1 : Real) <= d)
    (hbox : Pdual.shift z ''
        (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <=
      Edual.rectVertices (z 0 : Real)
        ((extentX : Real) + (z 0 : Real)) c d) :
    muDual.real (Edual.rectSideConnectionEvent 0 extentX 0 extentY
        (raw.data.dualLeftSource : Set W)
        (Edual.rectLeftBoundaryVertices 0 extentX 0 extentY)) *
      muDual.real (Edual.rectSideConnectionEvent 0 extentX 0 extentY
        (raw.data.dualRightSource : Set W)
        (Edual.rectRightBoundaryVertices 0 extentX 0 extentY)) -
      muDual.real (Pdual.pairMergeErrorUnion
        raw.data.dualLeftSource raw.data.dualRightSource radius) <=
      muDual.real (Edual.horizontalCrossingEvent
        (z 0 : Real) ((extentX : Real) + (z 0 : Real)) c d) := by
  let left := raw.data.dualLeftSource.image (Pdual.shift z)
  let right := raw.data.dualRightSource.image (Pdual.shift z)
  have hcarried := Edual.horizontalCrossing_ge_carriedComponents
    muDual hFKG (z 0 : Real) ((extentX : Real) + (z 0 : Real)) c d
    left right
    ((extentX : Real) + (z 0 : Real)) (z 1 : Real)
    ((extentY : Real) + (z 1 : Real)) (z 0 : Real) (z 1 : Real)
    ((extentY : Real) + (z 1 : Real))
    (z 0 : Real) ((extentX : Real) + (z 0 : Real)) c d
    le_rfl hc hd le_rfl hc hd le_rfl le_rfl le_rfl le_rfl
  have hmerge := raw.dualHorizontalMerge_translate_measureReal_le
    hTI z (z 0 : Real) ((extentX : Real) + (z 0 : Real)) c d
      radius hbox
  have hleft := Edual.rectLeftConnection_translate_measureReal_eq
    muDual hTI z 0 extentX 0 extentY
      (raw.data.dualLeftSource : Set W)
  have hright := Edual.rectRightConnection_translate_measureReal_eq
    muDual hTI z 0 extentX 0 extentY
      (raw.data.dualRightSource : Set W)
  have hleft' := hleft
  have hright' := hright
  simp only [zero_add] at hleft' hright'
  simp only [left, right, Finset.coe_image] at hcarried
  rw [hleft', hright'] at hcarried
  linarith


theorem dualVerticalCrossing_translate_inactive_tendsto_one
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG muDual) (hTI : Pdual.IsTranslationInvariant muDual)
    (S : Nat -> Finset V) (Sdual : Nat -> Finset W)
    (p pDual : Nat -> Real) (extentX extentY radius : Nat -> Nat)
    (raw : forall n, ExactExtentPairedMixedBoundaryScores
      E Edual mu muDual (S n) (Sdual n) (p n) (pDual n)
        (extentX n) (extentY n))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (z : Nat -> Site 2) (a b : Nat -> Real)
    (ha : forall n,
      a n <= (raw n).data.wideLeft + (z n 0 : Real))
    (hb : forall n,
      (raw n).data.wideRight + (z n 0 : Real) <= b n)
    (hbox : forall n, Pdual.shift (z n) ''
        (Pdual.orbitBox (Pdual.bufferedRadius (radius n)) : Set W) <=
      Edual.rectVertices (a n) (b n) (z n 1 : Real)
        ((extentY n : Real) + (z n 1 : Real)))
    (hmerge : Tendsto (fun n => muDual.real
      (Pdual.pairMergeErrorUnion (raw n).data.dualBottomSource
        (raw n).data.dualTopSource (radius n))) atTop (nhds 0)) :
    Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
      (a n) (b n) (z n 1 : Real)
        ((extentY n : Real) + (z n 1 : Real)))) atTop (nhds 1) := by
  let bottomScore : Nat -> Real := fun n => muDual.real
    (Edual.rectSideConnectionEvent
      (raw n).data.wideLeft (raw n).data.wideRight 0 (extentY n)
      ((raw n).data.dualBottomSource : Set W)
      (Edual.rectBottomBoundaryVertices
        (raw n).data.wideLeft (raw n).data.wideRight 0 (extentY n)))
  let topScore : Nat -> Real := fun n => muDual.real
    (Edual.rectSideConnectionEvent
      (raw n).data.wideLeft (raw n).data.wideRight 0 (extentY n)
      ((raw n).data.dualTopSource : Set W)
      (Edual.rectTopBoundaryVertices
        (raw n).data.wideLeft (raw n).data.wideRight 0 (extentY n)))
  have hbottom : Tendsto bottomScore atTop (nhds 1) :=
    hpDual.squeeze tendsto_const_nhds
      (fun n => by
        simpa [bottomScore, (raw n).shortTop_eq] using
          le_of_lt (raw n).data.dualBottomScore)
      (fun _ => measureReal_le_one)
  have htop : Tendsto topScore atTop (nhds 1) :=
    hpDual.squeeze tendsto_const_nhds
      (fun n => by
        simpa [topScore, (raw n).shortTop_eq] using
          le_of_lt (raw n).data.dualTopScore)
      (fun _ => measureReal_le_one)
  have hlower : Tendsto (fun n => bottomScore n * topScore n -
      muDual.real (Pdual.pairMergeErrorUnion
        (raw n).data.dualBottomSource (raw n).data.dualTopSource
          (radius n))) atTop (nhds 1) := by
    convert hbottom.mul htop |>.sub hmerge using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower tendsto_const_nhds
    (fun n => by
      simpa only [bottomScore, topScore] using
        (raw n).dualVerticalCrossing_ge_translate_inactive
          hFKG hTI (z n) (a n) (b n) (radius n)
            (ha n) (hb n) (hbox n))
    (fun _ => measureReal_le_one)


theorem dualHorizontalCrossing_translate_inactive_tendsto_one
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG muDual) (hTI : Pdual.IsTranslationInvariant muDual)
    (S : Nat -> Finset V) (Sdual : Nat -> Finset W)
    (p pDual : Nat -> Real) (extentX extentY radius : Nat -> Nat)
    (raw : forall n, ExactExtentPairedMixedBoundaryScores
      E Edual mu muDual (S n) (Sdual n) (p n) (pDual n)
        (extentX n) (extentY n))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (z : Nat -> Site 2) (c d : Nat -> Real)
    (hc : forall n, c n <= (z n 1 : Real))
    (hd : forall n, (extentY n : Real) + (z n 1 : Real) <= d n)
    (hbox : forall n, Pdual.shift (z n) ''
        (Pdual.orbitBox (Pdual.bufferedRadius (radius n)) : Set W) <=
      Edual.rectVertices (z n 0 : Real)
        ((extentX n : Real) + (z n 0 : Real)) (c n) (d n))
    (hmerge : Tendsto (fun n => muDual.real
      (Pdual.pairMergeErrorUnion (raw n).data.dualLeftSource
        (raw n).data.dualRightSource (radius n))) atTop (nhds 0)) :
    Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
      (z n 0 : Real) ((extentX n : Real) + (z n 0 : Real))
        (c n) (d n))) atTop (nhds 1) := by
  let leftScore : Nat -> Real := fun n => muDual.real
    (Edual.rectSideConnectionEvent 0 (extentX n) 0 (extentY n)
      ((raw n).data.dualLeftSource : Set W)
      (Edual.rectLeftBoundaryVertices 0 (extentX n) 0 (extentY n)))
  let rightScore : Nat -> Real := fun n => muDual.real
    (Edual.rectSideConnectionEvent 0 (extentX n) 0 (extentY n)
      ((raw n).data.dualRightSource : Set W)
      (Edual.rectRightBoundaryVertices 0 (extentX n) 0 (extentY n)))
  have hleft : Tendsto leftScore atTop (nhds 1) :=
    hpDual.squeeze tendsto_const_nhds
      (fun n => by
        simpa [leftScore, (raw n).narrowRight_eq,
          (raw n).tallTop_eq] using le_of_lt (raw n).data.dualLeftScore)
      (fun _ => measureReal_le_one)
  have hright : Tendsto rightScore atTop (nhds 1) :=
    hpDual.squeeze tendsto_const_nhds
      (fun n => by
        simpa [rightScore, (raw n).narrowRight_eq,
          (raw n).tallTop_eq] using le_of_lt (raw n).data.dualRightScore)
      (fun _ => measureReal_le_one)
  have hlower : Tendsto (fun n => leftScore n * rightScore n -
      muDual.real (Pdual.pairMergeErrorUnion
        (raw n).data.dualLeftSource (raw n).data.dualRightSource
          (radius n))) atTop (nhds 1) := by
    convert hleft.mul hright |>.sub hmerge using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower tendsto_const_nhds
    (fun n => by
      simpa only [leftScore, rightScore] using
        (raw n).dualHorizontalCrossing_ge_translate_inactive
          hFKG hTI (z n) (c n) (d n) (radius n)
            (hc n) (hd n) (hbox n))
    (fun _ => measureReal_le_one)


end StatMech.FK.PeriodicPlanar
