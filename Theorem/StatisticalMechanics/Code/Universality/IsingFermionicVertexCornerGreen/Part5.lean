/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
import Def.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen.Part5


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexLeftColumnCap_nonneg
    {n : Nat} (source x : FKIsingSquareFullVertexNode n) :
    0 <= vertexLeftColumnCap source x :=
  isingNatCappedTent_nonneg _ _

theorem vertexBottomRowRobinCap_nonneg
    {n : Nat} (source x : FKIsingSquareFullVertexNode n) :
    0 <= vertexBottomRowRobinCap source x :=
  isingNatCappedRobinTent_nonneg isingFermionicGhostCoefficient
    isingFermionicGhostCoefficient_pos _ _

theorem isingNatReverseCappedRobinTent_nonneg
    (coefficient : Real) (hcoefficient : 0 < coefficient)
    (top source i : Nat) :
    0 <= isingNatReverseCappedRobinTent coefficient top source i := by
  exact add_nonneg (isingNatReverseCappedTent_nonneg top source i)
    (one_div_nonneg.mpr hcoefficient.le)

theorem vertexTopRowRobinCap_nonneg
    (n : Nat) (source x : FKIsingSquareFullVertexNode n) :
    0 <= vertexTopRowRobinCap n source x :=
  isingNatReverseCappedRobinTent_nonneg isingFermionicGhostCoefficient
    isingFermionicGhostCoefficient_pos _ _ _

theorem isingNatReverseCappedRobinTent_secondDifference_nonpos
    (coefficient : Real) (top source i : Nat)
    (hi : 0 < i) (hitop : i < top) :
    isingNatReverseCappedRobinTent coefficient top source (i + 1) +
        isingNatReverseCappedRobinTent coefficient top source (i - 1) -
          2 * isingNatReverseCappedRobinTent coefficient top source i <= 0 := by
  unfold isingNatReverseCappedRobinTent
  have h := isingNatReverseCappedTent_secondDifference_nonpos
    top source i hi hitop
  linarith

theorem isingNatReverseCappedRobinTent_secondDifference_source
    (coefficient : Real) (top source : Nat)
    (hsource : 0 < source) (hsourceTop : source < top) :
    isingNatReverseCappedRobinTent coefficient top source (source + 1) +
        isingNatReverseCappedRobinTent coefficient top source (source - 1) -
          2 * isingNatReverseCappedRobinTent coefficient top source source =
      -1 := by
  unfold isingNatReverseCappedRobinTent
  have h := isingNatReverseCappedTent_secondDifference_source
    top source hsource hsourceTop
  linarith


theorem isingNatReverseCappedRobinTent_right_balance
    (coefficient : Real) (hcoefficient : 0 < coefficient)
    (top source : Nat) (hsourceTop : source < top) :
    isingNatReverseCappedRobinTent coefficient top source (top - 1) -
        isingNatReverseCappedRobinTent coefficient top source top -
          coefficient *
            isingNatReverseCappedRobinTent coefficient top source top = 0 := by
  unfold isingNatReverseCappedRobinTent isingNatReverseCappedTent
    isingNatCappedTent
  have htop : top - (top - 1) = 1 := by omega
  have hcap : 1 <= top - source := by omega
  simp [htop, hcap]
  field_simp [hcoefficient.ne']
  ring


theorem isingNatReverseCappedRobinTent_successor_sub_nonpos
    (coefficient : Real) (top source i : Nat) :
    isingNatReverseCappedRobinTent coefficient top source (i + 1) -
      isingNatReverseCappedRobinTent coefficient top source i <= 0 := by
  unfold isingNatReverseCappedRobinTent isingNatReverseCappedTent
  have hnext : top - (i + 1) = top - i - 1 := by omega
  rw [hnext]
  have h := isingNatCappedTent_predecessor_sub_nonpos
    (top - source) (top - i)
  linarith

theorem vertexLeftColumnCap_modifiedLaplacian_nonpos
    (n : Nat) (source x : FKIsingSquareFullVertexNode n)
    (hx : Not (fkIsingSquareFullVertexFixedBoundary n x)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (vertexLeftColumnCap source) x -
      isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) x *
        vertexLeftColumnCap source x <= 0 := by
  have hleft : -(n : Int) < x.1 0 := by
    have hb := (fkIsingSquareVertex_coordinate_bounds n x 0).1
    by_contra h
    apply hx
    simpa [fkIsingSquareFullVertexFixedBoundary,
      fkIsingSquareWiredArc] using (show x.1 0 = -(n : Int) by omega)
  have hindex : 0 < fullVertexColumnIndex n x := by
    have hcoe := fullVertexColumnIndex_coe n x
    omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => isingNatCappedTent (fullVertexColumnIndex n source)
          (fullVertexColumnIndex n y)) x -
      isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) x *
        isingNatCappedTent (fullVertexColumnIndex n source)
          (fullVertexColumnIndex n x) <= 0
  rw [fullVertexColumnFunction_laplacian n _ x hleft]
  by_cases hright : x.1 0 = (n : Int)
  · have hpred := isingNatCappedTent_predecessor_sub_nonpos
      (fullVertexColumnIndex n source) (fullVertexColumnIndex n x)
    have hkill : 0 <= isingFermionicGhostCoefficient *
        isingNatCappedTent (fullVertexColumnIndex n source)
          (fullVertexColumnIndex n x) :=
      mul_nonneg isingFermionicGhostCoefficient_pos.le
        (isingNatCappedTent_nonneg _ _)
    simp [hright, isingFermionicGhostRate,
      fullVertexRightGhostMultiplicity]
    linarith
  · have hsecond := isingNatCappedTent_secondDifference_nonpos
      (fullVertexColumnIndex n source) (fullVertexColumnIndex n x) hindex
    simpa [hright, isingFermionicGhostRate,
      fullVertexRightGhostMultiplicity] using hsecond

theorem vertexLeftColumnCap_modifiedLaplacian_source
    (n : Nat) (source : FKIsingSquareFullVertexNode n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (vertexLeftColumnCap source) source -
      isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) source *
        vertexLeftColumnCap source source = -1 := by
  have hleft : -(n : Int) < source.1 0 := by
    have hb := (fkIsingSquareVertex_coordinate_bounds n source 0).1
    by_contra h
    apply hfixed
    simpa [fkIsingSquareFullVertexFixedBoundary,
      fkIsingSquareWiredArc] using
        (show source.1 0 = -(n : Int) by omega)
  have hindex : 0 < fullVertexColumnIndex n source := by
    have hcoe := fullVertexColumnIndex_coe n source
    omega
  have hnotRight : Not (source.1 0 = (n : Int)) := by omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => isingNatCappedTent (fullVertexColumnIndex n source)
          (fullVertexColumnIndex n y)) source -
      isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) source *
        isingNatCappedTent (fullVertexColumnIndex n source)
          (fullVertexColumnIndex n source) = -1
  rw [fullVertexColumnFunction_laplacian n _ source hleft]
  simpa [hnotRight, isingFermionicGhostRate,
    fullVertexRightGhostMultiplicity] using
      isingNatCappedTent_secondDifference_source
        (fullVertexColumnIndex n source) hindex

theorem vertexBottomRowRobinCap_modifiedLaplacian_nonpos
    (n : Nat) (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n) (hsourceBottom : -(n : Int) < source.1 1) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (vertexBottomRowRobinCap source) x -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x *
        vertexBottomRowRobinCap source x <= 0 := by
  have hsourceIndex : 0 < fullVertexRowIndex n source := by
    have hcoe := fullVertexRowIndex_coe n source
    omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => isingNatCappedRobinTent isingFermionicGhostCoefficient
          (fullVertexRowIndex n source) (fullVertexRowIndex n y)) x -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x *
        isingNatCappedRobinTent isingFermionicGhostCoefficient
          (fullVertexRowIndex n source) (fullVertexRowIndex n x) <= 0
  rw [fullVertexRowFunction_laplacian n _ x hn]
  by_cases hbottom : x.1 1 = -(n : Int)
  · have hindex : fullVertexRowIndex n x = 0 := by
      have hcoe := fullVertexRowIndex_coe n x
      omega
    have hbalance := isingNatCappedRobinTent_left_balance
      isingFermionicGhostCoefficient isingFermionicGhostCoefficient_pos
      (fullVertexRowIndex n source) hsourceIndex
    simp [hbottom, hn.ne', hindex, isingFermionicGhostRate,
      fullVertexVerticalGhostMultiplicity] at hbalance ⊢
    linarith
  · by_cases htop : x.1 1 = (n : Int)
    · have hpred := isingNatCappedRobinTent_predecessor_sub_nonpos
        isingFermionicGhostCoefficient (fullVertexRowIndex n source)
          (fullVertexRowIndex n x)
      have hkill : 0 <= isingFermionicGhostCoefficient *
          isingNatCappedRobinTent isingFermionicGhostCoefficient
            (fullVertexRowIndex n source) (fullVertexRowIndex n x) :=
        mul_nonneg isingFermionicGhostCoefficient_pos.le
          (isingNatCappedRobinTent_nonneg isingFermionicGhostCoefficient
            isingFermionicGhostCoefficient_pos _ _)
      simp [htop, hn.ne', isingFermionicGhostRate,
        fullVertexVerticalGhostMultiplicity]
      linarith
    · have hindex : 0 < fullVertexRowIndex n x := by
        have hcoe := fullVertexRowIndex_coe n x
        omega
      have hsecond := isingNatCappedRobinTent_secondDifference_nonpos
        isingFermionicGhostCoefficient (fullVertexRowIndex n source)
          (fullVertexRowIndex n x) hindex
      simpa [hbottom, htop, isingFermionicGhostRate,
        fullVertexVerticalGhostMultiplicity] using hsecond

theorem vertexBottomRowRobinCap_modifiedLaplacian_source
    (n : Nat) (source : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (vertexBottomRowRobinCap source) source -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) source *
        vertexBottomRowRobinCap source source = -1 := by
  have hindex : 0 < fullVertexRowIndex n source := by
    have hcoe := fullVertexRowIndex_coe n source
    omega
  have hnotBottom : Not (source.1 1 = -(n : Int)) := by omega
  have hnotTop : Not (source.1 1 = (n : Int)) := by omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => isingNatCappedRobinTent isingFermionicGhostCoefficient
          (fullVertexRowIndex n source) (fullVertexRowIndex n y)) source -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) source *
        isingNatCappedRobinTent isingFermionicGhostCoefficient
          (fullVertexRowIndex n source) (fullVertexRowIndex n source) = -1
  rw [fullVertexRowFunction_laplacian n _ source hn]
  simpa [hnotBottom, hnotTop, isingFermionicGhostRate,
    fullVertexVerticalGhostMultiplicity] using
      isingNatCappedRobinTent_secondDifference_source
        isingFermionicGhostCoefficient (fullVertexRowIndex n source) hindex

theorem vertexTopRowRobinCap_modifiedLaplacian_nonpos
    (n : Nat) (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n) (hsourceTop : source.1 1 < (n : Int)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (vertexTopRowRobinCap n source) x -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x *
        vertexTopRowRobinCap n source x <= 0 := by
  have hsourceIndex : fullVertexRowIndex n source < 2 * n := by
    have hcoe := fullVertexRowIndex_coe n source
    exact_mod_cast (show (fullVertexRowIndex n source : Int) <
        2 * (n : Int) by omega)
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => isingNatReverseCappedRobinTent
          isingFermionicGhostCoefficient (2 * n)
          (fullVertexRowIndex n source) (fullVertexRowIndex n y)) x -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x *
        isingNatReverseCappedRobinTent isingFermionicGhostCoefficient (2 * n)
          (fullVertexRowIndex n source) (fullVertexRowIndex n x) <= 0
  rw [fullVertexRowFunction_laplacian n _ x hn]
  by_cases hbottom : x.1 1 = -(n : Int)
  · have hindex : fullVertexRowIndex n x = 0 := by
      have hcoe := fullVertexRowIndex_coe n x
      omega
    have hsucc := isingNatReverseCappedRobinTent_successor_sub_nonpos
      isingFermionicGhostCoefficient (2 * n) (fullVertexRowIndex n source)
        (fullVertexRowIndex n x)
    have hkill : 0 <= isingFermionicGhostCoefficient *
        isingNatReverseCappedRobinTent isingFermionicGhostCoefficient (2 * n)
          (fullVertexRowIndex n source) (fullVertexRowIndex n x) :=
      mul_nonneg isingFermionicGhostCoefficient_pos.le
        (isingNatReverseCappedRobinTent_nonneg
          isingFermionicGhostCoefficient isingFermionicGhostCoefficient_pos
          _ _ _)
    simp [hbottom, hn.ne', isingFermionicGhostRate,
      fullVertexVerticalGhostMultiplicity]
    linarith
  · by_cases htop : x.1 1 = (n : Int)
    · have hindex : fullVertexRowIndex n x = 2 * n := by
        have hcoe := fullVertexRowIndex_coe n x
        exact_mod_cast (show (fullVertexRowIndex n x : Int) =
            2 * (n : Int) by omega)
      have hbalance := isingNatReverseCappedRobinTent_right_balance
        isingFermionicGhostCoefficient isingFermionicGhostCoefficient_pos
        (2 * n) (fullVertexRowIndex n source) hsourceIndex
      simp [htop, hn.ne', hindex, isingFermionicGhostRate,
        fullVertexVerticalGhostMultiplicity] at hbalance ⊢
      linarith
    · have hindexPos : 0 < fullVertexRowIndex n x := by
        have hcoe := fullVertexRowIndex_coe n x
        omega
      have hindexTop : fullVertexRowIndex n x < 2 * n := by
        have hcoe := fullVertexRowIndex_coe n x
        have hxBound := (fkIsingSquareVertex_coordinate_bounds n x 1).2
        have hint : (fullVertexRowIndex n x : Int) <
            ((2 * n : Nat) : Int) := by
          push_cast
          omega
        exact_mod_cast hint
      have hsecond :=
        isingNatReverseCappedRobinTent_secondDifference_nonpos
          isingFermionicGhostCoefficient (2 * n)
          (fullVertexRowIndex n source) (fullVertexRowIndex n x)
          hindexPos hindexTop
      simpa [hbottom, htop, isingFermionicGhostRate,
        fullVertexVerticalGhostMultiplicity] using hsecond

theorem vertexTopRowRobinCap_modifiedLaplacian_source
    (n : Nat) (source : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (vertexTopRowRobinCap n source) source -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) source *
        vertexTopRowRobinCap n source source = -1 := by
  have hindexPos : 0 < fullVertexRowIndex n source := by
    have hcoe := fullVertexRowIndex_coe n source
    omega
  have hindexTop : fullVertexRowIndex n source < 2 * n := by
    have hcoe := fullVertexRowIndex_coe n source
    exact_mod_cast (show (fullVertexRowIndex n source : Int) <
        2 * (n : Int) by omega)
  have hnotBottom : Not (source.1 1 = -(n : Int)) := by omega
  have hnotTop : Not (source.1 1 = (n : Int)) := by omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => isingNatReverseCappedRobinTent
          isingFermionicGhostCoefficient (2 * n)
          (fullVertexRowIndex n source) (fullVertexRowIndex n y)) source -
      isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) source *
        isingNatReverseCappedRobinTent isingFermionicGhostCoefficient (2 * n)
          (fullVertexRowIndex n source) (fullVertexRowIndex n source) = -1
  rw [fullVertexRowFunction_laplacian n _ source hn]
  simpa [hnotBottom, hnotTop, isingFermionicGhostRate,
    fullVertexVerticalGhostMultiplicity] using
      isingNatReverseCappedRobinTent_secondDifference_source
        isingFermionicGhostCoefficient (2 * n)
        (fullVertexRowIndex n source) hindexPos hindexTop

theorem fullVertex_adj_columnIndex_eq_or_rowIndex_eq
    (n : Nat) (x y : FKIsingSquareFullVertexNode n)
    (hxy : (fkIsingSquareFullVertexGraph n).Adj x y) :
    fullVertexColumnIndex n x = fullVertexColumnIndex n y ∨
      fullVertexRowIndex n x = fullVertexRowIndex n y := by
  change (hypercubicLattice 2).Adj x.1 y.1 at hxy
  rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
  · right
    apply Int.ofNat_inj.mp
    rw [fullVertexRowIndex_coe, fullVertexRowIndex_coe]
    have hk := congrFun h 1
    simp [Pi.add_apply] at hk
    omega
  · right
    apply Int.ofNat_inj.mp
    rw [fullVertexRowIndex_coe, fullVertexRowIndex_coe]
    have hk := congrFun h 1
    simp [Pi.add_apply] at hk
    omega
  · left
    apply Int.ofNat_inj.mp
    rw [fullVertexColumnIndex_coe, fullVertexColumnIndex_coe]
    have hk := congrFun h 0
    simp [Pi.add_apply] at hk
    omega
  · left
    apply Int.ofNat_inj.mp
    rw [fullVertexColumnIndex_coe, fullVertexColumnIndex_coe]
    have hk := congrFun h 0
    simp [Pi.add_apply] at hk
    omega

theorem vertexLowerCornerCaps_edgewise
    (n : Nat) (source x y : FKIsingSquareFullVertexNode n)
    (hxy : (fkIsingSquareFullVertexGraph n).Adj x y) :
    (vertexLeftColumnCap source y - vertexLeftColumnCap source x) *
        (vertexBottomRowRobinCap source y -
          vertexBottomRowRobinCap source x) = 0 := by
  rcases fullVertex_adj_columnIndex_eq_or_rowIndex_eq n x y hxy with hcol | hrow
  · simp [vertexLeftColumnCap, hcol]
  · simp [vertexBottomRowRobinCap, hrow]

theorem vertexUpperCornerCaps_edgewise
    (n : Nat) (source x y : FKIsingSquareFullVertexNode n)
    (hxy : (fkIsingSquareFullVertexGraph n).Adj x y) :
    (vertexLeftColumnCap source y - vertexLeftColumnCap source x) *
        (vertexTopRowRobinCap n source y -
          vertexTopRowRobinCap n source x) = 0 := by
  rcases fullVertex_adj_columnIndex_eq_or_rowIndex_eq n x y hxy with hcol | hrow
  · simp [vertexLeftColumnCap, hcol]
  · simp [vertexTopRowRobinCap, hrow]


theorem vertexPointPoissonBarrier_le_lowerLeftProduct
    (n : Nat) (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int)) :
    vertexPointPoissonBarrier n (some source) (some x) <=
      vertexLeftColumnCap source x * vertexBottomRowRobinCap source x /
        (vertexLeftColumnCap source source +
          vertexBottomRowRobinCap source source) := by
  letI : Nonempty (FKIsingSquareFullVertexNode n) := ⟨source⟩
  have hreach : forall c : FKIsingSquareFullVertexNode n, exists b,
      (fkIsingSquareFullVertexFixedBoundary n b ∨
        0 < isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) b) ∧
        (fkIsingSquareFullVertexGraph n).Reachable c b := by
    intro c
    obtain ⟨b, hb, hcb⟩ := fkIsingSquareFullVertex_reaches_fixed_or_ghost n c
    refine ⟨b, ?_, hcb⟩
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr ((isingFermionicGhostRate_pos_iff
        (fkIsingSquareFullVertexGhostMultiplicity n) b).2 hb)
  have hleft : -(n : Int) < source.1 0 := by
    have hb := (fkIsingSquareVertex_coordinate_bounds n source 0).1
    by_contra h
    apply hfixed
    simpa [fkIsingSquareFullVertexFixedBoundary,
      fkIsingSquareWiredArc] using
        (show source.1 0 = -(n : Int) by omega)
  have hcolIndex : 0 < fullVertexColumnIndex n source := by
    have hcoe := fullVertexColumnIndex_coe n source
    omega
  have hden : 0 < vertexLeftColumnCap source source +
      vertexBottomRowRobinCap source source := by
    have hcol : 0 < vertexLeftColumnCap source source := by
      simpa [vertexLeftColumnCap, isingNatCappedTent_self] using
        (show (0 : Real) < fullVertexColumnIndex n source by positivity)
    linarith [vertexBottomRowRobinCap_nonneg source source]
  change isingFiniteWeightedPointPoissonBarrier
      (isingFiniteGhostGraph (fkIsingSquareFullVertexGraph n)
        (isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n)))
      (isingFiniteGhostConductance (fkIsingSquareFullVertexGraph n)
        (isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n)))
      (isingFiniteGhostBoundaryWith
        (fkIsingSquareFullVertexFixedBoundary n))
      _ _ _ (some source) (some x) <= _
  apply isingFiniteGhostPointPoissonBarrier_le_splitProduct
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n))
    (isingFermionicGhostRate (fullVertexRightGhostMultiplicity n))
    (isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n))
    (fkIsingSquareFullVertexFixedBoundary n)
  · exact isingFermionicGhostRate_nonneg _
  · exact fullVertexGhostRate_split n
  · exact hreach
  · exact hfixed
  · exact vertexLeftColumnCap_nonneg source
  · exact vertexBottomRowRobinCap_nonneg source
  · exact hden
  · exact vertexLowerCornerCaps_edgewise n source
  · intro c hc
    exact vertexLeftColumnCap_modifiedLaplacian_nonpos n source c hc
  · intro c _hc
    exact vertexBottomRowRobinCap_modifiedLaplacian_nonpos
      n source c hn hbottom
  · exact (vertexLeftColumnCap_modifiedLaplacian_source
      n source hfixed hright).le
  · exact (vertexBottomRowRobinCap_modifiedLaplacian_source
      n source hn hbottom htop).le


theorem vertexPointPoissonBarrier_le_upperLeftProduct
    (n : Nat) (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int)) :
    vertexPointPoissonBarrier n (some source) (some x) <=
      vertexLeftColumnCap source x * vertexTopRowRobinCap n source x /
        (vertexLeftColumnCap source source +
          vertexTopRowRobinCap n source source) := by
  letI : Nonempty (FKIsingSquareFullVertexNode n) := ⟨source⟩
  have hreach : forall c : FKIsingSquareFullVertexNode n, exists b,
      (fkIsingSquareFullVertexFixedBoundary n b ∨
        0 < isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) b) ∧
        (fkIsingSquareFullVertexGraph n).Reachable c b := by
    intro c
    obtain ⟨b, hb, hcb⟩ := fkIsingSquareFullVertex_reaches_fixed_or_ghost n c
    refine ⟨b, ?_, hcb⟩
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr ((isingFermionicGhostRate_pos_iff
        (fkIsingSquareFullVertexGhostMultiplicity n) b).2 hb)
  have hleft : -(n : Int) < source.1 0 := by
    have hb := (fkIsingSquareVertex_coordinate_bounds n source 0).1
    by_contra h
    apply hfixed
    simpa [fkIsingSquareFullVertexFixedBoundary,
      fkIsingSquareWiredArc] using
        (show source.1 0 = -(n : Int) by omega)
  have hcolIndex : 0 < fullVertexColumnIndex n source := by
    have hcoe := fullVertexColumnIndex_coe n source
    omega
  have hden : 0 < vertexLeftColumnCap source source +
      vertexTopRowRobinCap n source source := by
    have hcol : 0 < vertexLeftColumnCap source source := by
      simpa [vertexLeftColumnCap, isingNatCappedTent_self] using
        (show (0 : Real) < fullVertexColumnIndex n source by positivity)
    linarith [vertexTopRowRobinCap_nonneg n source source]
  change isingFiniteWeightedPointPoissonBarrier
      (isingFiniteGhostGraph (fkIsingSquareFullVertexGraph n)
        (isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n)))
      (isingFiniteGhostConductance (fkIsingSquareFullVertexGraph n)
        (isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n)))
      (isingFiniteGhostBoundaryWith
        (fkIsingSquareFullVertexFixedBoundary n))
      _ _ _ (some source) (some x) <= _
  apply isingFiniteGhostPointPoissonBarrier_le_splitProduct
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n))
    (isingFermionicGhostRate (fullVertexRightGhostMultiplicity n))
    (isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n))
    (fkIsingSquareFullVertexFixedBoundary n)
  · exact isingFermionicGhostRate_nonneg _
  · exact fullVertexGhostRate_split n
  · exact hreach
  · exact hfixed
  · exact vertexLeftColumnCap_nonneg source
  · exact vertexTopRowRobinCap_nonneg n source
  · exact hden
  · exact vertexUpperCornerCaps_edgewise n source
  · intro c hc
    exact vertexLeftColumnCap_modifiedLaplacian_nonpos n source c hc
  · intro c _hc
    exact vertexTopRowRobinCap_modifiedLaplacian_nonpos n source c hn htop
  · exact (vertexLeftColumnCap_modifiedLaplacian_source
      n source hfixed hright).le
  · exact (vertexTopRowRobinCap_modifiedLaplacian_source
      n source hn hbottom htop).le


theorem vertexMarkedEndpointLayer_coordinate_cases
    (n radius : Nat) (x : FKIsingSquareFullVertexNode n)
    (hx : vertexMarkedEndpointLayer n radius (some x)) :
    fullVertexColumnIndex n x + fullVertexRowIndex n x <= radius ∨
      fullVertexColumnIndex n x +
        (2 * n - fullVertexRowIndex n x) <= radius := by
  change Int.natAbs (x.1 0 + (n : Int)) +
        Int.natAbs (x.1 1 + (n : Int)) <= radius ∨
      Int.natAbs (x.1 0 + (n : Int)) +
        Int.natAbs (x.1 1 - (n : Int)) <= radius at hx
  have hx0nonneg : 0 <= x.1 0 + (n : Int) := by
    have hb := (fkIsingSquareVertex_coordinate_bounds n x 0).1
    omega
  have hx1nonneg : 0 <= x.1 1 + (n : Int) := by
    have hb := (fkIsingSquareVertex_coordinate_bounds n x 1).1
    omega
  have hx0abs : Int.natAbs (x.1 0 + (n : Int)) =
      fullVertexColumnIndex n x := by
    apply Int.ofNat_inj.mp
    rw [Int.natAbs_of_nonneg hx0nonneg, fullVertexColumnIndex_coe]
  have hx1abs : Int.natAbs (x.1 1 + (n : Int)) =
      fullVertexRowIndex n x := by
    apply Int.ofNat_inj.mp
    rw [Int.natAbs_of_nonneg hx1nonneg, fullVertexRowIndex_coe]
  have htopabs : Int.natAbs (x.1 1 - (n : Int)) =
      2 * n - fullVertexRowIndex n x := by
    have hrow := fullVertexRowIndex_le n x
    have hnonneg : 0 <= (n : Int) - x.1 1 := by
      have hb := (fkIsingSquareVertex_coordinate_bounds n x 1).2
      omega
    apply Int.ofNat_inj.mp
    rw [show x.1 1 - (n : Int) = -((n : Int) - x.1 1) by ring,
      Int.natAbs_neg, Int.natAbs_of_nonneg hnonneg,
      Nat.cast_sub hrow, fullVertexRowIndex_coe]
    push_cast
    ring
  rcases hx with hx | hx
  · exact Or.inl (by simpa [hx0abs, hx1abs] using hx)
  · exact Or.inr (by simpa [hx0abs, htopabs] using hx)


theorem vertexPointPoissonBarrier_le_lowerLeftRadius
    (n radius : Nat) (distance : Real)
    (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int))
    (hcorner : fullVertexColumnIndex n x + fullVertexRowIndex n x <= radius)
    (hdistance : 0 < distance)
    (hsourceDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (fullVertexRowIndex n source : Real) +
          1 / isingFermionicGhostCoefficient) :
    vertexPointPoissonBarrier n (some source) (some x) <=
      (radius : Real) *
        ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance := by
  have hgreen := vertexPointPoissonBarrier_le_lowerLeftProduct
    n source x hn hfixed hright hbottom htop
  have hcolCoord : (fullVertexColumnIndex n x : Real) <= radius := by
    exact_mod_cast (show fullVertexColumnIndex n x <= radius by omega)
  have hrowCoord : (fullVertexRowIndex n x : Real) <= radius := by
    exact_mod_cast (show fullVertexRowIndex n x <= radius by omega)
  have hcol : vertexLeftColumnCap source x <= (radius : Real) := by
    exact (isingNatCappedTent_le_coordinate
      (fullVertexColumnIndex n source) (fullVertexColumnIndex n x)).trans
        hcolCoord
  have hrow : vertexBottomRowRobinCap source x <=
      (radius : Real) + 1 / isingFermionicGhostCoefficient := by
    unfold vertexBottomRowRobinCap isingNatCappedRobinTent
    have htent := isingNatCappedTent_le_coordinate
      (fullVertexRowIndex n source) (fullVertexRowIndex n x)
    linarith
  have hrow0 := vertexBottomRowRobinCap_nonneg source x
  have hbound0 : 0 <= (radius : Real) *
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) :=
    mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (Nat.cast_nonneg _)
        (one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le))
  have hnum : vertexLeftColumnCap source x *
      vertexBottomRowRobinCap source x <=
        (radius : Real) *
          ((radius : Real) + 1 / isingFermionicGhostCoefficient) :=
    mul_le_mul hcol hrow hrow0 (Nat.cast_nonneg _)
  have hden : distance <= vertexLeftColumnCap source source +
      vertexBottomRowRobinCap source source := by
    have heq : vertexLeftColumnCap source source +
        vertexBottomRowRobinCap source source =
          (fullVertexColumnIndex n source : Real) +
            (fullVertexRowIndex n source : Real) +
              1 / isingFermionicGhostCoefficient := by
      simp [vertexLeftColumnCap, vertexBottomRowRobinCap,
        isingNatCappedRobinTent, isingNatCappedTent_self]
      ring
    rw [heq]
    exact hsourceDistance
  exact hgreen.trans (div_le_div₀ hbound0 hnum hdistance hden)


theorem vertexPointPoissonBarrier_le_upperLeftRadius
    (n radius : Nat) (distance : Real)
    (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int))
    (hcorner : fullVertexColumnIndex n x +
      (2 * n - fullVertexRowIndex n x) <= radius)
    (hdistance : 0 < distance)
    (hsourceDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (2 * n - fullVertexRowIndex n source : Nat) +
          1 / isingFermionicGhostCoefficient) :
    vertexPointPoissonBarrier n (some source) (some x) <=
      (radius : Real) *
        ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance := by
  have hgreen := vertexPointPoissonBarrier_le_upperLeftProduct
    n source x hn hfixed hright hbottom htop
  have hcolCoord : (fullVertexColumnIndex n x : Real) <= radius := by
    exact_mod_cast (show fullVertexColumnIndex n x <= radius by omega)
  have hrowCoord : ((2 * n - fullVertexRowIndex n x : Nat) : Real) <=
      radius := by
    exact_mod_cast (show 2 * n - fullVertexRowIndex n x <= radius by omega)
  have hcol : vertexLeftColumnCap source x <= (radius : Real) := by
    exact (isingNatCappedTent_le_coordinate
      (fullVertexColumnIndex n source) (fullVertexColumnIndex n x)).trans
        hcolCoord
  have hrow : vertexTopRowRobinCap n source x <=
      (radius : Real) + 1 / isingFermionicGhostCoefficient := by
    unfold vertexTopRowRobinCap isingNatReverseCappedRobinTent
    have htent := isingNatReverseCappedTent_le_coordinate
      (2 * n) (fullVertexRowIndex n source) (fullVertexRowIndex n x)
    linarith
  have hrow0 := vertexTopRowRobinCap_nonneg n source x
  have hbound0 : 0 <= (radius : Real) *
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) :=
    mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (Nat.cast_nonneg _)
        (one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le))
  have hnum : vertexLeftColumnCap source x *
      vertexTopRowRobinCap n source x <=
        (radius : Real) *
          ((radius : Real) + 1 / isingFermionicGhostCoefficient) :=
    mul_le_mul hcol hrow hrow0 (Nat.cast_nonneg _)
  have hden : distance <= vertexLeftColumnCap source source +
      vertexTopRowRobinCap n source source := by
    have heq : vertexLeftColumnCap source source +
        vertexTopRowRobinCap n source source =
          (fullVertexColumnIndex n source : Real) +
            (2 * n - fullVertexRowIndex n source : Nat) +
              1 / isingFermionicGhostCoefficient := by
      simp [vertexLeftColumnCap, vertexTopRowRobinCap,
        isingNatReverseCappedRobinTent, isingNatCappedTent_self,
        isingNatReverseCappedTent_self]
      ring
    rw [heq]
    exact hsourceDistance
  exact hgreen.trans (div_le_div₀ hbound0 hnum hdistance hden)


theorem vertexPointPoissonBarrier_le_markedEndpointRadius
    (n radius : Nat) (distance : Real)
    (source x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int))
    (hx : vertexMarkedEndpointLayer n radius (some x))
    (hdistance : 0 < distance)
    (hlowerDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (fullVertexRowIndex n source : Real) +
          1 / isingFermionicGhostCoefficient)
    (hupperDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (2 * n - fullVertexRowIndex n source : Nat) +
          1 / isingFermionicGhostCoefficient) :
    vertexPointPoissonBarrier n (some source) (some x) <=
      (radius : Real) *
        ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance := by
  rcases vertexMarkedEndpointLayer_coordinate_cases n radius x hx with
    hlower | hupper
  · exact vertexPointPoissonBarrier_le_lowerLeftRadius
      n radius distance source x hn hfixed hright hbottom htop hlower
        hdistance hlowerDistance
  · exact vertexPointPoissonBarrier_le_upperLeftRadius
      n radius distance source x hn hfixed hright hbottom htop hupper
        hdistance hupperDistance


theorem vertexPointPoissonBarrier_le_exceptionalSourceRadius
    (n radius : Nat) (distance : Real)
    (source : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int))
    (hdistance : 0 < distance)
    (hlowerDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (fullVertexRowIndex n source : Real) +
          1 / isingFermionicGhostCoefficient)
    (hupperDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (2 * n - fullVertexRowIndex n source : Nat) +
          1 / isingFermionicGhostCoefficient) :
    forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources
        (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius) ->
      vertexPointPoissonBarrier n (some source) z <=
        (radius : Real) *
          ((radius : Real) + 1 / isingFermionicGhostCoefficient) /
            distance := by
  intro z hz
  have hmarked : vertexMarkedEndpointLayer n radius z := by
    have hz' : Not (vertexDirichletBoundary n z) ∧
        vertexMarkedEndpointLayer n radius z := by
      simpa [isingFiniteWeightedInteriorExceptionalSources] using hz
    exact hz'.2
  cases z with
  | none => exact False.elim hmarked
  | some x =>
      exact vertexPointPoissonBarrier_le_markedEndpointRadius
        n radius distance source x hn hfixed hright hbottom htop hmarked
          hdistance hlowerDistance hupperDistance

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
