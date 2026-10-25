/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.template_subset
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    {S : Finset V} {width height M : Nat} {p : Real}
    (data : E.CommonSquareBoundaryBandData mu S width height M p)
    (v : PreferenceGridVertex width height) :
    ((P.fourShiftTemplate S data.zLeft data.zRight
        data.zBottom data.zTop).image
        (P.shift (preferenceGridSite v)) : Set V) ⊆
      E.rectVertices (-(M : Real)) M (-(M : Real)) M := by
  intro x hx
  change x ∈ (P.fourShiftTemplate S data.zLeft data.zRight
    data.zBottom data.zTop).image (P.shift (preferenceGridSite v)) at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  simp only [PeriodicGraph.fourShiftTemplate, Finset.mem_union] at hy
  rcases hy with (hy | hy) | (hy | hy)
  · exact (data.left v).1 (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  · exact (data.right v).1 (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  · exact (data.bottom v).1 (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  · exact (data.top v).1 (Finset.mem_image.mpr ⟨y, hy, rfl⟩)


theorem PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.leftScore_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {S : Finset V} {width height M : Nat} {p : Real}
    (data : E.CommonSquareBoundaryBandData mu S width height M p)
    (v : PreferenceGridVertex width height) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) M (-(M : Real)) M
      ((P.fourShiftTemplate S data.zLeft data.zRight
        data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices
        (-(M : Real)) M (-(M : Real)) M)) := by
  refine (data.left v).2.trans_le (measureReal_mono
    (E.rectSideConnectionEvent_mono_source ?_))
  intro x hx
  change x ∈ (S.image (P.shift data.zLeft)).image
    (P.shift (preferenceGridSite v)) at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y,
    P.image_subset_fourShiftTemplate S data.zLeft data.zRight
      data.zBottom data.zTop hy, rfl⟩

theorem PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.rightScore_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {S : Finset V} {width height M : Nat} {p : Real}
    (data : E.CommonSquareBoundaryBandData mu S width height M p)
    (v : PreferenceGridVertex width height) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) M (-(M : Real)) M
      ((P.fourShiftTemplate S data.zLeft data.zRight
        data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices
        (-(M : Real)) M (-(M : Real)) M)) := by
  refine (data.right v).2.trans_le (measureReal_mono
    (E.rectSideConnectionEvent_mono_source ?_))
  intro x hx
  change x ∈ (S.image (P.shift data.zRight)).image
    (P.shift (preferenceGridSite v)) at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y,
    P.image_right_subset_fourShiftTemplate S data.zLeft data.zRight
      data.zBottom data.zTop hy, rfl⟩

theorem PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.bottomScore_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {S : Finset V} {width height M : Nat} {p : Real}
    (data : E.CommonSquareBoundaryBandData mu S width height M p)
    (v : PreferenceGridVertex width height) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) M (-(M : Real)) M
      ((P.fourShiftTemplate S data.zLeft data.zRight
        data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices
        (-(M : Real)) M (-(M : Real)) M)) := by
  refine (data.bottom v).2.trans_le (measureReal_mono
    (E.rectSideConnectionEvent_mono_source ?_))
  intro x hx
  change x ∈ (S.image (P.shift data.zBottom)).image
    (P.shift (preferenceGridSite v)) at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y,
    P.image_bottom_subset_fourShiftTemplate S data.zLeft data.zRight
      data.zBottom data.zTop hy, rfl⟩

theorem PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.topScore_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {S : Finset V} {width height M : Nat} {p : Real}
    (data : E.CommonSquareBoundaryBandData mu S width height M p)
    (v : PreferenceGridVertex width height) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) M (-(M : Real)) M
      ((P.fourShiftTemplate S data.zLeft data.zRight
        data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices
        (-(M : Real)) M (-(M : Real)) M)) := by
  refine (data.top v).2.trans_le (measureReal_mono
    (E.rectSideConnectionEvent_mono_source ?_))
  intro x hx
  change x ∈ (S.image (P.shift data.zTop)).image
    (P.shift (preferenceGridSite v)) at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y,
    P.image_top_subset_fourShiftTemplate S data.zLeft data.zRight
      data.zBottom data.zTop hy, rfl⟩

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


theorem exists_matched_commonSquareBoundaryBandData
    (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W))) [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {width height : Nat}
    {p pDual : Real}
    (primal : E.BoundaryBandSeed mu S width height p)
    (dual : Edual.BoundaryBandSeed muDual Sdual width height pDual) :
    ∃ M : Nat,
      Nonempty (E.CommonSquareBoundaryBandData
        mu S width height M p) ∧
      Nonempty (Edual.CommonSquareBoundaryBandData
        muDual Sdual width height M pDual) := by
  let M := commonPrimalDualBandHalfWidth
    primal.radiusLeft primal.radiusRight
    primal.radiusBottom primal.radiusTop
    dual.radiusLeft dual.radiusRight dual.radiusBottom dual.radiusTop
  have h := le_commonPrimalDualBandHalfWidth
    primal.radiusLeft primal.radiusRight
    primal.radiusBottom primal.radiusTop
    dual.radiusLeft dual.radiusRight dual.radiusBottom dual.radiusTop
  dsimp only at h
  exact ⟨M,
    ⟨primal.toCommonSquare E mu hTI M h.1 h.2.1 h.2.2.1 h.2.2.2.1⟩,
    ⟨dual.toCommonSquare Edual muDual hTIDual M
      h.2.2.2.2.1 h.2.2.2.2.2.1
      h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2⟩⟩


end StatMech.FK.PeriodicPlanar
