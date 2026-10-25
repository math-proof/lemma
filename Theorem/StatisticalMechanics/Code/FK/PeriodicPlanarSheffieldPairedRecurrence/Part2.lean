/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem ExactExtentPairedMixedBoundaryScores.enlargeWideRight
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    [IsFiniteMeasure mu] [IsFiniteMeasure muDual]
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (newRight : Int) (hRight : raw.wideRightInt <= newRight) :
    Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY) := by
  let data := raw.data
  have hWide : data.wideRight <= (newRight : Real) := by
    rw [raw.wideRight_eq]
    exact_mod_cast hRight
  let enlarged : PairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual := {
    width := data.width
    height := data.height
    widthDual := data.widthDual
    heightDual := data.heightDual
    width_pos := data.width_pos
    height_pos := data.height_pos
    widthDual_pos := data.widthDual_pos
    heightDual_pos := data.heightDual_pos
    base := data.base
    baseDual := data.baseDual
    narrowRight := data.narrowRight
    shortTop := data.shortTop
    wideLeft := data.wideLeft
    wideRight := newRight
    tallTop := data.tallTop
    wideLeft_le := data.wideLeft_le
    narrowRight_le := data.narrowRight_le.trans hWide
    shortTop_le := data.shortTop_le
    primal_bottom := fun i => (data.primal_bottom i).trans_le
      (measureReal_mono (E.rectBottomConnectionEvent_mono_otherBounds _
        le_rfl hWide le_rfl))
    primal_top := fun i => (data.primal_top i).trans_le
      (measureReal_mono (E.rectTopConnectionEvent_mono_otherBounds _
        le_rfl hWide le_rfl))
    primal_left := data.primal_left
    primal_right := data.primal_right
    dual_bottom := fun i => (data.dual_bottom i).trans_le
      (measureReal_mono (Edual.rectBottomConnectionEvent_mono_otherBounds _
        le_rfl hWide le_rfl))
    dual_top := fun i => (data.dual_top i).trans_le
      (measureReal_mono (Edual.rectTopConnectionEvent_mono_otherBounds _
        le_rfl hWide le_rfl))
    dual_left := data.dual_left
    dual_right := data.dual_right }
  exact ⟨{
    data := enlarged
    wideLeftInt := raw.wideLeftInt
    wideRightInt := newRight
    narrowRight_eq := raw.narrowRight_eq
    shortTop_eq := raw.shortTop_eq
    tallTop_eq := raw.tallTop_eq
    wideLeft_eq := raw.wideLeft_eq
    wideRight_eq := rfl }⟩


theorem ExactExtentPairedMixedBoundaryScores.enlargeWide
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    [IsFiniteMeasure mu] [IsFiniteMeasure muDual]
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (newLeft newRight : Int)
    (hLeft : newLeft <= raw.wideLeftInt)
    (hRight : raw.wideRightInt <= newRight) :
    Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY) := by
  let data := raw.data
  have hWideLeft : (newLeft : Real) <= data.wideLeft := by
    rw [raw.wideLeft_eq]
    exact_mod_cast hLeft
  have hWideRight : data.wideRight <= (newRight : Real) := by
    rw [raw.wideRight_eq]
    exact_mod_cast hRight
  let enlarged : PairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual := {
    width := data.width
    height := data.height
    widthDual := data.widthDual
    heightDual := data.heightDual
    width_pos := data.width_pos
    height_pos := data.height_pos
    widthDual_pos := data.widthDual_pos
    heightDual_pos := data.heightDual_pos
    base := data.base
    baseDual := data.baseDual
    narrowRight := data.narrowRight
    shortTop := data.shortTop
    wideLeft := newLeft
    wideRight := newRight
    tallTop := data.tallTop
    wideLeft_le := hWideLeft.trans data.wideLeft_le
    narrowRight_le := data.narrowRight_le.trans hWideRight
    shortTop_le := data.shortTop_le
    primal_bottom := fun i => (data.primal_bottom i).trans_le
      (measureReal_mono (E.rectBottomConnectionEvent_mono_otherBounds _
        hWideLeft hWideRight le_rfl))
    primal_top := fun i => (data.primal_top i).trans_le
      (measureReal_mono (E.rectTopConnectionEvent_mono_otherBounds _
        hWideLeft hWideRight le_rfl))
    primal_left := data.primal_left
    primal_right := data.primal_right
    dual_bottom := fun i => (data.dual_bottom i).trans_le
      (measureReal_mono (Edual.rectBottomConnectionEvent_mono_otherBounds _
        hWideLeft hWideRight le_rfl))
    dual_top := fun i => (data.dual_top i).trans_le
      (measureReal_mono (Edual.rectTopConnectionEvent_mono_otherBounds _
        hWideLeft hWideRight le_rfl))
    dual_left := data.dual_left
    dual_right := data.dual_right }
  exact ⟨{
    data := enlarged
    wideLeftInt := newLeft
    wideRightInt := newRight
    narrowRight_eq := raw.narrowRight_eq
    shortTop_eq := raw.shortTop_eq
    tallTop_eq := raw.tallTop_eq
    wideLeft_eq := rfl
    wideRight_eq := rfl }⟩


theorem ExactExtentPairedMixedBoundaryScores.primalConnector_subset_narrow
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY radius : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hleft : (E.connectorMarginRequirement radius : Int) <= raw.data.base 0)
    (hright : raw.data.base 0 + raw.data.width +
      E.connectorMarginRequirement radius <= extentX)
    (hbottom : (E.connectorMarginRequirement radius : Int) <= raw.data.base 1)
    (htop : raw.data.base 1 + raw.data.height +
      E.connectorMarginRequirement radius <= extentY) :
    forall v : PreferenceGridVertex raw.data.width raw.data.height,
      P.shift (raw.data.base + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
        E.rectVertices 0 extentX 0 extentY := by
  intro v
  have hgrid := E.preferenceGrid_orbitBox_subset_translated_rect
    (P.bufferedRadius radius) (E.connectorMarginRequirement radius)
    raw.data.width raw.data.height raw.data.base
    (E.orbitBoxCoordinateBound_le_connectorMarginRequirement radius 0)
    (E.orbitBoxCoordinateBound_le_connectorMarginRequirement radius 1) v
  have hleftR : (E.connectorMarginRequirement radius : Real) <=
      raw.data.base 0 := by exact_mod_cast hleft
  have hrightR : (raw.data.base 0 : Real) + raw.data.width +
      E.connectorMarginRequirement radius <= extentX := by exact_mod_cast hright
  have hbottomR : (E.connectorMarginRequirement radius : Real) <=
      raw.data.base 1 := by exact_mod_cast hbottom
  have htopR : (raw.data.base 1 : Real) + raw.data.height +
      E.connectorMarginRequirement radius <= extentY := by exact_mod_cast htop
  have hmono : E.rectVertices
      (-(E.connectorMarginRequirement radius : Real) + raw.data.base 0)
      (E.connectorMarginRequirement radius + raw.data.width + raw.data.base 0)
      (-(E.connectorMarginRequirement radius : Real) + raw.data.base 1)
      (E.connectorMarginRequirement radius + raw.data.height + raw.data.base 1) ⊆
      E.rectVertices 0 extentX 0 extentY := by
    apply E.rectVertices_mono <;> push_cast <;> linarith
  simpa [add_comm] using hgrid.trans hmono


theorem ExactExtentPairedMixedBoundaryScores.dualConnector_subset_narrow
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY radius : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hleft : (Edual.connectorMarginRequirement radius : Int) <=
      raw.data.baseDual 0)
    (hright : raw.data.baseDual 0 + raw.data.widthDual +
      Edual.connectorMarginRequirement radius <= extentX)
    (hbottom : (Edual.connectorMarginRequirement radius : Int) <=
      raw.data.baseDual 1)
    (htop : raw.data.baseDual 1 + raw.data.heightDual +
      Edual.connectorMarginRequirement radius <= extentY) :
    forall v : PreferenceGridVertex raw.data.widthDual raw.data.heightDual,
      Pdual.shift (raw.data.baseDual + preferenceGridSite v) ''
          (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) ⊆
        Edual.rectVertices 0 extentX 0 extentY := by
  intro v
  have hgrid := Edual.preferenceGrid_orbitBox_subset_translated_rect
    (Pdual.bufferedRadius radius) (Edual.connectorMarginRequirement radius)
    raw.data.widthDual raw.data.heightDual raw.data.baseDual
    (Edual.orbitBoxCoordinateBound_le_connectorMarginRequirement radius 0)
    (Edual.orbitBoxCoordinateBound_le_connectorMarginRequirement radius 1) v
  have hleftR : (Edual.connectorMarginRequirement radius : Real) <=
      raw.data.baseDual 0 := by exact_mod_cast hleft
  have hrightR : (raw.data.baseDual 0 : Real) + raw.data.widthDual +
      Edual.connectorMarginRequirement radius <= extentX := by
    exact_mod_cast hright
  have hbottomR : (Edual.connectorMarginRequirement radius : Real) <=
      raw.data.baseDual 1 := by exact_mod_cast hbottom
  have htopR : (raw.data.baseDual 1 : Real) + raw.data.heightDual +
      Edual.connectorMarginRequirement radius <= extentY := by
    exact_mod_cast htop
  have hmono : Edual.rectVertices
      (-(Edual.connectorMarginRequirement radius : Real) + raw.data.baseDual 0)
      (Edual.connectorMarginRequirement radius + raw.data.widthDual +
        raw.data.baseDual 0)
      (-(Edual.connectorMarginRequirement radius : Real) + raw.data.baseDual 1)
      (Edual.connectorMarginRequirement radius + raw.data.heightDual +
        raw.data.baseDual 1) ⊆ Edual.rectVertices 0 extentX 0 extentY := by
    apply Edual.rectVertices_mono <;> push_cast <;> linarith
  simpa [add_comm] using hgrid.trans hmono


theorem ExactExtentPairedMixedBoundaryScores.primalConnector_subset_wide
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY radius : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hleft : (E.connectorMarginRequirement radius : Int) <= raw.data.base 0)
    (hright : raw.data.base 0 + raw.data.width +
      E.connectorMarginRequirement radius <= extentX)
    (hbottom : (E.connectorMarginRequirement radius : Int) <= raw.data.base 1)
    (htop : raw.data.base 1 + raw.data.height +
      E.connectorMarginRequirement radius <= extentY) :
    forall v : PreferenceGridVertex raw.data.width raw.data.height,
      P.shift (raw.data.base + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
        E.rectVertices raw.data.wideLeft raw.data.wideRight
          0 raw.data.shortTop := by
  intro v
  apply (raw.primalConnector_subset_narrow hleft hright hbottom htop v).trans
  apply E.rectVertices_mono
  · exact raw.data.wideLeft_le
  · simpa [raw.narrowRight_eq] using raw.data.narrowRight_le
  · exact le_rfl
  · rw [raw.shortTop_eq]


theorem ExactExtentPairedMixedBoundaryScores.dualConnector_subset_wide
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {extentX extentY radius : Nat}
    (raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual extentX extentY)
    (hleft : (Edual.connectorMarginRequirement radius : Int) <=
      raw.data.baseDual 0)
    (hright : raw.data.baseDual 0 + raw.data.widthDual +
      Edual.connectorMarginRequirement radius <= extentX)
    (hbottom : (Edual.connectorMarginRequirement radius : Int) <=
      raw.data.baseDual 1)
    (htop : raw.data.baseDual 1 + raw.data.heightDual +
      Edual.connectorMarginRequirement radius <= extentY) :
    forall v : PreferenceGridVertex raw.data.widthDual raw.data.heightDual,
      Pdual.shift (raw.data.baseDual + preferenceGridSite v) ''
          (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) ⊆
        Edual.rectVertices raw.data.wideLeft raw.data.wideRight
          0 raw.data.shortTop := by
  intro v
  apply (raw.dualConnector_subset_narrow hleft hright hbottom htop v).trans
  apply Edual.rectVertices_mono
  · exact raw.data.wideLeft_le
  · simpa [raw.narrowRight_eq] using raw.data.narrowRight_le
  · exact le_rfl
  · rw [raw.shortTop_eq]


end StatMech.FK.PeriodicPlanar
