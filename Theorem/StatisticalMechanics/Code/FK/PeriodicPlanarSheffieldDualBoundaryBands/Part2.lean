/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualBoundaryBands.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRecursiveLimits
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNormalBoundaryBandAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonSquareEnlarge
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualBoundaryBands.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem exists_pairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat → Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k : Nat) :
    Nonempty (PairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual) := by
  let h := schedule.horizontal k
  let v := schedule.vertical k
  let minimumX := max
    (max (family.radiusLeft h) (family.radiusRight h))
    (max (familyDual.radiusLeft h) (familyDual.radiusRight h))
  let minimumY := max
    (max (family.radiusBottom v) (family.radiusTop v))
    (max (familyDual.radiusBottom v) (familyDual.radiusTop v))
  obtain ⟨extentX, extentY, width, height, widthDual, heightDual,
      hminX, hminY, hwidth, hheight, hwidthDual, hheightDual,
      hb, hbDual, hd, hdDual⟩ :=
    exists_pairedMixedGridDimensions E Edual family familyDual
      h v minimumX minimumY
  let base : Site 2 := fun i ↦ if i = 0 then
    family.baseLeft 0 + h else family.baseBottom 1 + v
  let baseDual : Site 2 := fun i ↦ if i = 0 then
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
  let topLowerDual : Int := baseDual 0 - familyDual.baseTop 0 -
    familyDual.radiusTop v
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
  have hleftP : (family.radiusLeft h : Int) ≤ extentX := by
    exact_mod_cast (Nat.le_max_left _ _ |>.trans
      (Nat.le_max_left _ _) |>.trans hminX)
  have hrightP : (family.radiusRight h : Int) ≤ extentX := by
    exact_mod_cast (Nat.le_max_right _ _ |>.trans
      (Nat.le_max_left _ _) |>.trans hminX)
  have hbottomP : (family.radiusBottom v : Int) ≤ extentY := by
    exact_mod_cast (Nat.le_max_left _ _ |>.trans
      (Nat.le_max_left _ _) |>.trans hminY)
  have htopP : (family.radiusTop v : Int) ≤ extentY := by
    exact_mod_cast (Nat.le_max_right _ _ |>.trans
      (Nat.le_max_left _ _) |>.trans hminY)
  have hleftD : (familyDual.radiusLeft h : Int) ≤ extentX := by
    exact_mod_cast (Nat.le_max_left _ _ |>.trans
      (Nat.le_max_right _ _) |>.trans hminX)
  have hrightD : (familyDual.radiusRight h : Int) ≤ extentX := by
    exact_mod_cast (Nat.le_max_right _ _ |>.trans
      (Nat.le_max_right _ _) |>.trans hminX)
  have hbottomD : (familyDual.radiusBottom v : Int) ≤ extentY := by
    exact_mod_cast (Nat.le_max_left _ _ |>.trans
      (Nat.le_max_right _ _) |>.trans hminY)
  have htopD : (familyDual.radiusTop v : Int) ≤ extentY := by
    exact_mod_cast (Nat.le_max_right _ _ |>.trans
      (Nat.le_max_right _ _) |>.trans hminY)
  have hmixedP := family.mixedBoundaryScores E mu hTI h v width height
    (schedule.primal_left_bottom k) (schedule.primal_right_bottom k)
    (by simpa [base, hb] using hleftP)
    (by simpa [base, hb] using hrightP)
    (by simpa [base, hd] using hbottomP)
    (by simpa [base, hd] using htopP)
  have hmixedD := familyDual.mixedBoundaryScores Edual muDual hTIDual
    h v widthDual heightDual (schedule.dual_left_bottom k)
    (schedule.dual_right_bottom k)
    (by simpa [baseDual, hbDual] using hleftD)
    (by simpa [baseDual, hbDual] using hrightD)
    (by simpa [baseDual, hdDual] using hbottomD)
    (by simpa [baseDual, hdDual] using htopD)
  dsimp only at hmixedP hmixedD
  simp only [if_pos (rfl : (0 : Fin 2) = 0),
    if_neg (by decide : (1 : Fin 2) ≠ 0), if_true, if_false]
      at hmixedP hmixedD
  rw [hb, hd] at hmixedP
  rw [hbDual, hdDual] at hmixedD
  change (((aP : Real) ≤ 0 ∧ (extentX : Real) ≤ bP ∧
      (0 : Real) ≤ 0 ∧ (extentY : Real) ≤ dP) ∧ _) at hmixedP
  change (((aD : Real) ≤ 0 ∧ (extentX : Real) ≤ bD ∧
      (0 : Real) ≤ 0 ∧ (extentY : Real) ≤ dD) ∧ _) at hmixedD
  refine ⟨{
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
      have hmin : (a : Real) ≤ (aP : Real) := by
        exact_mod_cast min_le_left aP aD
      exact hmin.trans hmixedP.1.1
    narrowRight_le := by
      have hmax : (bP : Real) ≤ (b : Real) := by
        exact_mod_cast le_max_left bP bD
      exact hmixedP.1.2.1.trans hmax
    shortTop_le := by
      have hmax : (dP : Real) ≤ (d : Real) := by
        exact_mod_cast le_max_left dP dD
      exact hmixedP.1.2.2.2.trans hmax
    primal_bottom := ?_
    primal_top := ?_
    primal_left := ?_
    primal_right := ?_
    dual_bottom := ?_
    dual_top := ?_
    dual_left := ?_
    dual_right := ?_ }⟩
  · intro i
    exact (hmixedP.2.1 i).trans_le (measureReal_mono
      (E.rectBottomConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_left aP aD)
        (by exact_mod_cast le_max_left bP bD) le_rfl))
  · intro i
    exact (hmixedP.2.2.1 i).trans_le (measureReal_mono
      (E.rectTopConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_left aP aD)
        (by exact_mod_cast le_max_left bP bD) le_rfl))
  · intro j
    exact (hmixedP.2.2.2.1 j).trans_le (measureReal_mono
      (E.rectLeftConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_left dP dD)))
  · intro j
    exact (hmixedP.2.2.2.2 j).trans_le (measureReal_mono
      (E.rectRightConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_left dP dD)))
  · intro i
    exact (hmixedD.2.1 i).trans_le (measureReal_mono
      (Edual.rectBottomConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_right aP aD)
        (by exact_mod_cast le_max_right bP bD) le_rfl))
  · intro i
    exact (hmixedD.2.2.1 i).trans_le (measureReal_mono
      (Edual.rectTopConnectionEvent_mono_otherBounds _
        (by exact_mod_cast min_le_right aP aD)
        (by exact_mod_cast le_max_right bP bD) le_rfl))
  · intro j
    exact (hmixedD.2.2.2.1 j).trans_le (measureReal_mono
      (Edual.rectLeftConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_right dP dD)))
  · intro j
    exact (hmixedD.2.2.2.2 j).trans_le (measureReal_mono
      (Edual.rectRightConnectionEvent_mono_otherBounds _ le_rfl le_rfl
        (by exact_mod_cast le_max_right dP dD)))


theorem exists_pairedCofinalNormalBoundaryBandFamilies_bounded
    (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W))) [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
    ∃ (p pDual : Nat → Real)
      (family : ∀ m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m))
      (familyDual : ∀ m,
        Edual.NormalBoundaryBandFamily muDual
          (Pdual.orbitBox m) (pDual m)),
      Tendsto p atTop (nhds 1) ∧
      (∀ m, p m ≤ 1) ∧
      Tendsto pDual atTop (nhds 1) ∧
      (∀ m, pDual m ≤ 1) := by
  obtain ⟨p, family, hp, hp_le⟩ :=
    E.exists_cofinalNormalBoundaryBandFamilies_bounded
      mu hFKG hTI hunique
  obtain ⟨pDual, familyDual, hpDual, hpDual_le⟩ :=
    Edual.exists_cofinalNormalBoundaryBandFamilies_bounded
      muDual hFKGDual hTIDual huniqueDual
  exact ⟨p, pDual, family, familyDual,
    hp, hp_le, hpDual, hpDual_le⟩


theorem exists_pairedCofinalMatchedCommonSquareNormalBoundaryBandData
    (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W))) [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (margin : Nat → Nat) :
    ∃ (p pDual : Nat → Real)
      (family : ∀ m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m))
      (familyDual : ∀ m,
        Edual.NormalBoundaryBandFamily muDual
          (Pdual.orbitBox m) (pDual m))
      (M : Nat → Nat),
      (∀ m, Nonempty (E.CommonSquareNormalBoundaryBandData
        mu (P.orbitBox m) (margin m) (M m) (p m))) ∧
      (∀ m, Nonempty (Edual.CommonSquareNormalBoundaryBandData
        muDual (Pdual.orbitBox m) (margin m) (M m) (pDual m))) ∧
      Tendsto p atTop (nhds 1) ∧
      (∀ m, p m ≤ 1) ∧
      Tendsto pDual atTop (nhds 1) ∧
      (∀ m, pDual m ≤ 1) := by
  obtain ⟨p, pDual, family, familyDual,
      hp, hp_le, hpDual, hpDual_le⟩ :=
    exists_pairedCofinalNormalBoundaryBandFamilies_bounded
      E Edual mu muDual hFKG hTI hunique hFKGDual hTIDual huniqueDual
  have hmatched (m : Nat) :
      ∃ M : Nat,
        Nonempty (E.CommonSquareNormalBoundaryBandData
          mu (P.orbitBox m) (margin m) M (p m)) ∧
        Nonempty (Edual.CommonSquareNormalBoundaryBandData
          muDual (Pdual.orbitBox m) (margin m) M (pDual m)) :=
    exists_matched_commonSquareNormalBoundaryBandData E Edual mu muDual
      hTI hTIDual ((family m).seed E (margin m))
        ((familyDual m).seed Edual (margin m))
  let M : Nat → Nat := fun m ↦ Classical.choose (hmatched m)
  have hdata (m : Nat) := Classical.choose_spec (hmatched m)
  exact ⟨p, pDual, family, familyDual, M,
    fun m ↦ (hdata m).1, fun m ↦ (hdata m).2,
    hp, hp_le, hpDual, hpDual_le⟩


theorem exists_pairedUniformConnectorRadii_with_commonHalfWidthData
    (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W))) [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
    ∃ (radius radiusDual : Nat → Nat),
      E.UniformConnectorCrossingRadius mu radius ∧
      Edual.UniformConnectorCrossingRadius muDual radiusDual ∧
      ∃ (primal : E.ConnectorReadyCommonSquareData mu radius)
        (dual : Edual.ConnectorReadyCommonSquareData muDual radiusDual),
        primal.M = dual.M := by
  obtain ⟨radius, hradius, ⟨primal⟩⟩ :=
    E.exists_uniformConnectorRadius_with_commonSquare
      mu hFKG hTI hunique
  obtain ⟨radiusDual, hradiusDual, ⟨dual⟩⟩ :=
    Edual.exists_uniformConnectorRadius_with_commonSquare
      muDual hFKGDual hTIDual huniqueDual
  obtain ⟨primal', dual', hprimalM, hdualM⟩ :=
    exists_commonHalfWidth_connectorReadyData
      E Edual hTI hTIDual primal dual
  exact ⟨radius, radiusDual, hradius, hradiusDual,
    primal', dual', hprimalM.trans hdualM.symm⟩


theorem PeriodicPlanarDualPair.exists_canonicalMatchedBoundaryBands_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hcommon :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1)
    (margin : Nat → Nat) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    let muDual : Measure (ConfigSpace (Sym2 W)) := D.dualMeasure mu
    ∃ (score scoreDual : Nat → Real)
      (family : ∀ m, D.primalEmbedding.NormalBoundaryBandFamily
        mu (P.orbitBox m) (score m))
      (familyDual : ∀ m, D.dualEmbedding.NormalBoundaryBandFamily
        muDual (Pdual.orbitBox m) (scoreDual m))
      (M : Nat → Nat),
      (∀ m, Nonempty
        (D.primalEmbedding.CommonSquareNormalBoundaryBandData
          mu (P.orbitBox m) (margin m) (M m) (score m))) ∧
      (∀ m, Nonempty
        (D.dualEmbedding.CommonSquareNormalBoundaryBandData
          muDual (Pdual.orbitBox m) (margin m) (M m) (scoreDual m))) ∧
      Tendsto score atTop (nhds 1) ∧
      (∀ m, score m ≤ 1) ∧
      Tendsto scoreDual atTop (nhds 1) ∧
      (∀ m, scoreDual m ≤ 1) := by
  dsimp only
  letI : IsProbabilityMeasure
      (D.dualMeasure
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V)))) :=
    inferInstance
  have hdata := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  exact exists_pairedCofinalMatchedCommonSquareNormalBoundaryBandData
    D.primalEmbedding D.dualEmbedding _ _
      hdata.1 hdata.2.1 hdata.2.2.2.2.1
      hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.2
      margin


theorem PeriodicPlanarDualPair.exists_canonicalConnectorReadyData_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hcommon :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    let muDual : Measure (ConfigSpace (Sym2 W)) := D.dualMeasure mu
    ∃ (radius radiusDual : Nat → Nat),
      D.primalEmbedding.UniformConnectorCrossingRadius mu radius ∧
      D.dualEmbedding.UniformConnectorCrossingRadius muDual radiusDual ∧
      ∃ (primal : D.primalEmbedding.ConnectorReadyCommonSquareData
          mu radius)
        (dual : D.dualEmbedding.ConnectorReadyCommonSquareData
          muDual radiusDual),
        primal.M = dual.M := by
  dsimp only
  letI : IsProbabilityMeasure
      (D.dualMeasure
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V)))) :=
    inferInstance
  have hdata := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  exact exists_pairedUniformConnectorRadii_with_commonHalfWidthData
    D.primalEmbedding D.dualEmbedding _ _
      hdata.1 hdata.2.1 hdata.2.2.2.2.1
      hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.2

end StatMech.FK.PeriodicPlanar
