/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldConnectorReadyCommonSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldConnectorReadyCommonSquare
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicPlaneEmbedding.exists_connectorReadyCommonSquareData
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (radius : Nat -> Nat) :
    Nonempty (E.ConnectorReadyCommonSquareData mu radius) := by
  let buffer : Nat -> Nat := fun n =>
    max n (P.bufferedRadius (radius n))
  have hbuffer (n : Nat) : n <= buffer n := Nat.le_max_left _ _
  obtain ⟨M, baseL, baseR, baseB, baseT,
      hleft, hright, hbottom, htop,
      hleftLimit, hrightLimit, hbottomLimit, htopLimit⟩ :=
    E.exists_commonSquare_fourBoundaryPlacements
      mu hFKG hTI hunique buffer hbuffer
  let zLeft : Nat -> Site 2 := fun n => baseL n + commonRectLeftShift M n
  let zRight : Nat -> Site 2 := fun n => baseR n + commonRectRightShift M n
  let zBottom : Nat -> Site 2 := fun n => baseB n + commonRectBottomShift M n
  let zTop : Nat -> Site 2 := fun n => baseT n + commonRectTopShift M n
  have hshiftSet (z b : Site 2) (S : Set V) :
      P.shift z '' (P.shift b '' S) = P.shift (b + z) '' S := by
    rw [Set.image_image]
    apply congrArg (fun f : V -> V => f '' S)
    funext x
    exact (P.shift_add b z x).symm
  have hleft' (n : Nat) :
      P.shift (zLeft n) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    dsimp only [zLeft]
    rw [← hshiftSet]
    exact (Set.image_mono (Set.image_mono (fun v hv =>
      P.orbitBox_mono (Nat.le_max_right _ _) hv))).trans (hleft n)
  have hright' (n : Nat) :
      P.shift (zRight n) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    dsimp only [zRight]
    rw [← hshiftSet]
    exact (Set.image_mono (Set.image_mono (fun v hv =>
      P.orbitBox_mono (Nat.le_max_right _ _) hv))).trans (hright n)
  have hbottom' (n : Nat) :
      P.shift (zBottom n) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    dsimp only [zBottom]
    rw [← hshiftSet]
    exact (Set.image_mono (Set.image_mono (fun v hv =>
      P.orbitBox_mono (Nat.le_max_right _ _) hv))).trans (hbottom n)
  have htop' (n : Nat) :
      P.shift (zTop n) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    dsimp only [zTop]
    rw [← hshiftSet]
    exact (Set.image_mono (Set.image_mono (fun v hv =>
      P.orbitBox_mono (Nat.le_max_right _ _) hv))).trans (htop n)
  refine ⟨{
    M := M
    baseLeft := zLeft
    baseRight := zRight
    baseBottom := zBottom
    baseTop := zTop
    connectorLeft := hleft'
    connectorRight := hright'
    connectorBottom := hbottom'
    connectorTop := htop'
    leftLimit := ?_
    rightLimit := ?_
    bottomLimit := ?_
    topLimit := ?_ }⟩
  · simpa only [zLeft, ← hshiftSet] using hleftLimit
  · simpa only [zRight, ← hshiftSet] using hrightLimit
  · simpa only [zBottom, ← hshiftSet] using hbottomLimit
  · simpa only [zTop, ← hshiftSet] using htopLimit


theorem PeriodicPlaneEmbedding.exists_uniformConnectorRadius_with_commonSquare
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    exists radius : Nat -> Nat,
      E.UniformConnectorCrossingRadius mu radius ∧
        Nonempty (E.ConnectorReadyCommonSquareData mu radius) := by
  obtain ⟨radius, hradius⟩ :=
    E.exists_uniform_connectorRadius_crossing_max_tendsto_one
      mu hFKG hTI hunique
  exact ⟨radius, hradius,
    E.exists_connectorReadyCommonSquareData
      mu hFKG hTI hunique radius⟩

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


theorem exists_matchedPreferenceGrid_connectorContainment
    (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {radius radiusDual : Nat -> Nat}
    (primal : E.ConnectorReadyCommonSquareData mu radius)
    (dual : Edual.ConnectorReadyCommonSquareData muDual radiusDual) :
    let commonM : Nat -> Nat := fun n => max (primal.M n) (dual.M n)
    exists extentX extentY : Nat -> Nat,
      (forall n, 0 < primal.baseRight n 0 + (extentX n : Int) -
        primal.baseLeft n 0) ∧
      (forall n, 0 < dual.baseRight n 0 + (extentX n : Int) -
        dual.baseLeft n 0) ∧
      (forall n, 0 < primal.baseTop n 1 + (extentY n : Int) -
        primal.baseBottom n 1) ∧
      (forall n, 0 < dual.baseTop n 1 + (extentY n : Int) -
        dual.baseBottom n 1) ∧
      (forall n (v : PreferenceGridVertex
          (boundaryGridWidth (extentX n) (primal.baseLeft n)
            (primal.baseRight n))
          (boundaryGridHeight (extentY n) (primal.baseBottom n)
            (primal.baseTop n))),
        P.shift (boundaryGridBase (primal.baseLeft n) (primal.baseBottom n) +
            preferenceGridSite v) ''
            (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
          E.rectVertices (-(commonM n : Real))
            (commonM n + extentX n : Real) (-(commonM n : Real))
            (commonM n + extentY n : Real)) ∧
      (forall n (v : PreferenceGridVertex
          (boundaryGridWidth (extentX n) (dual.baseLeft n)
            (dual.baseRight n))
          (boundaryGridHeight (extentY n) (dual.baseBottom n)
            (dual.baseTop n))),
        Pdual.shift (boundaryGridBase (dual.baseLeft n) (dual.baseBottom n) +
            preferenceGridSite v) ''
            (Pdual.orbitBox
              (Pdual.bufferedRadius (radiusDual n)) : Set W) ⊆
          Edual.rectVertices (-(commonM n : Real))
            (commonM n + extentX n : Real) (-(commonM n : Real))
            (commonM n + extentY n : Real)) := by
  dsimp only
  choose extentX extentY _hminX _hminY hpX hdX hpY hdY using fun n =>
    exists_commonPreferenceExtents_ge
      (primal.baseLeft n) (primal.baseRight n)
      (primal.baseBottom n) (primal.baseTop n)
      (dual.baseLeft n) (dual.baseRight n)
      (dual.baseBottom n) (dual.baseTop n) 0 0
  refine ⟨extentX, extentY, hpX, hdX, hpY, hdY, ?_, ?_⟩
  · intro n
    let commonM := max (primal.M n) (dual.M n)
    have hle : primal.M n <= commonM := Nat.le_max_left _ _
    have hleR : (primal.M n : Real) <= commonM := by exact_mod_cast hle
    have henlarge : E.rectVertices (-(primal.M n : Real))
        (primal.M n : Real) (-(primal.M n : Real)) (primal.M n : Real) ⊆
      E.rectVertices (-(commonM : Real)) (commonM : Real)
        (-(commonM : Real)) (commonM : Real) := by
      apply E.rectVertices_mono <;> linarith
    exact E.preferenceGrid_translatedSet_subset_rect_of_commonSquare
      commonM (extentX n) (extentY n)
      (primal.baseLeft n) (primal.baseRight n)
      (primal.baseBottom n) (primal.baseTop n)
      (hpX n) (hpY n)
      (P.orbitBox (P.bufferedRadius (radius n)) : Set V)
      ((primal.connectorLeft n).trans henlarge)
      ((primal.connectorRight n).trans henlarge)
      ((primal.connectorBottom n).trans henlarge)
      ((primal.connectorTop n).trans henlarge)
  · intro n
    let commonM := max (primal.M n) (dual.M n)
    have hle : dual.M n <= commonM := Nat.le_max_right _ _
    have hleR : (dual.M n : Real) <= commonM := by exact_mod_cast hle
    have henlarge : Edual.rectVertices (-(dual.M n : Real))
        (dual.M n : Real) (-(dual.M n : Real)) (dual.M n : Real) ⊆
      Edual.rectVertices (-(commonM : Real)) (commonM : Real)
        (-(commonM : Real)) (commonM : Real) := by
      apply Edual.rectVertices_mono <;> linarith
    exact Edual.preferenceGrid_translatedSet_subset_rect_of_commonSquare
      commonM (extentX n) (extentY n)
      (dual.baseLeft n) (dual.baseRight n)
      (dual.baseBottom n) (dual.baseTop n)
      (hdX n) (hdY n)
      (Pdual.orbitBox
        (Pdual.bufferedRadius (radiusDual n)) : Set W)
      ((dual.connectorLeft n).trans henlarge)
      ((dual.connectorRight n).trans henlarge)
      ((dual.connectorBottom n).trans henlarge)
      ((dual.connectorTop n).trans henlarge)

end StatMech.FK.PeriodicPlanar
