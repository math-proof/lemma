/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerGreen


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem faceRobinColumnCap_nonneg
    {n : Nat} (source c : FKIsingSquareFullFaceNode n) :
    0 <= faceRobinColumnCap source c := by
  exact isingNatCappedRobinTent_nonneg
    isingFermionicGhostCoefficient isingFermionicGhostCoefficient_pos
    source.1.1 c.1.1

theorem faceBottomRowCap_nonneg
    {n : Nat} (source c : FKIsingSquareFullFaceNode n) :
    0 <= faceBottomRowCap source c :=
  isingNatCappedTent_nonneg source.2.1 c.2.1


theorem faceMarkedEndpointLayer_coordinate_cases
    (n radius : Nat) (c : FKIsingSquareFullFaceNode n)
    (hc : faceMarkedEndpointLayer n radius (some c)) :
    c.1.1 + c.2.1 <= radius \/
      c.1.1 + (2 * n - 1 - c.2.1) <= radius := by
  change Int.natAbs
        ((-(n : Int) + c.1.1) + (n : Int)) +
          Int.natAbs ((-(n : Int) + c.2.1) + (n : Int)) <= radius \/
      Int.natAbs ((-(n : Int) + c.1.1) + (n : Int)) +
          Int.natAbs ((-(n : Int) + c.2.1) - (n : Int)) <= radius at hc
  rcases hc with hc | hc
  · left
    simpa using hc
  · right
    have hy := c.2.isLt
    have hxabs : Int.natAbs
        ((-(n : Int) + c.1.1) + (n : Int)) = c.1.1 := by
      rw [show (-(n : Int) + c.1.1) + (n : Int) = (c.1.1 : Int) by
        omega]
      simp
    have habs : Int.natAbs
        ((-(n : Int) + c.2.1) - (n : Int)) = 2 * n - c.2.1 := by
      have hnonneg : 0 <= 2 * (n : Int) - c.2.1 := by omega
      have hcast : ((Int.natAbs (2 * (n : Int) - c.2.1) : Nat) : Int) =
          ((2 * n - c.2.1 : Nat) : Int) := by
        rw [Int.natAbs_of_nonneg hnonneg]
        rw [Nat.cast_sub (by omega : c.2.1 <= 2 * n)]
        push_cast
        rfl
      have hnat : Int.natAbs (2 * (n : Int) - c.2.1) =
          2 * n - c.2.1 := by
        exact_mod_cast hcast
      rw [show (-(n : Int) + c.2.1) - (n : Int) =
          -(2 * (n : Int) - c.2.1) by ring,
        Int.natAbs_neg, hnat]
    rw [hxabs, habs] at hc
    omega

theorem faceRobinColumnCap_modifiedLaplacian_nonpos
    (n : Nat) (source c : FKIsingSquareFullFaceNode n)
    (hsource : 0 < source.1.1)
    (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (faceRobinColumnCap source) c -
      isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
        faceRobinColumnCap source c <= 0 := by
  change isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun d => isingNatCappedRobinTent isingFermionicGhostCoefficient
        source.1.1 d.1.1) c -
      isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
        isingNatCappedRobinTent isingFermionicGhostCoefficient
          source.1.1 c.1.1 <= 0
  rw [faceColumnFunction_laplacian_of_not_fixed n _ c hc]
  by_cases hleft : c.1.1 = 0
  · have hbal := isingNatCappedRobinTent_left_balance
      isingFermionicGhostCoefficient isingFermionicGhostCoefficient_pos
      source.1.1 hsource
    simp [hleft, isingFermionicGhostRate,
      fkIsingSquareFullFaceGhostMultiplicity] at hbal ⊢
    linarith
  · have hwest : 0 < c.1.1 := by omega
    have hsecond := isingNatCappedRobinTent_secondDifference_nonpos
      isingFermionicGhostCoefficient source.1.1 c.1.1 hwest
    simp [hleft, isingFermionicGhostRate,
      fkIsingSquareFullFaceGhostMultiplicity] at hsecond ⊢
    exact hsecond

theorem faceBottomRowCap_laplacian_nonpos
    (n : Nat) (source c : FKIsingSquareFullFaceNode n)
    (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (faceBottomRowCap source) c <= 0 := by
  have hsouth : 0 < c.2.1 := by
    by_contra h
    apply hc
    left
    omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
    (fun d => isingNatCappedTent source.2.1 d.2.1) c <= 0
  rw [faceRowFunction_laplacian_of_not_fixed n _ c hc]
  exact isingNatCappedTent_secondDifference_nonpos
    source.2.1 c.2.1 hsouth

theorem faceRobinColumnCap_modifiedLaplacian_source
    (n : Nat) (source : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
    (hleft : 0 < source.1.1) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (faceRobinColumnCap source) source -
      isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) source *
        faceRobinColumnCap source source = -1 := by
  change isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun d => isingNatCappedRobinTent isingFermionicGhostCoefficient
        source.1.1 d.1.1) source -
      isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) source *
        isingNatCappedRobinTent isingFermionicGhostCoefficient
          source.1.1 source.1.1 = -1
  rw [faceColumnFunction_laplacian_of_not_fixed n _ source hfixed]
  have hsecond := isingNatCappedRobinTent_secondDifference_source
    isingFermionicGhostCoefficient source.1.1 hleft
  simp [Nat.ne_of_gt hleft, isingFermionicGhostRate,
    fkIsingSquareFullFaceGhostMultiplicity] at hsecond ⊢
  exact hsecond

theorem faceBottomRowCap_laplacian_source
    (n : Nat) (source : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (faceBottomRowCap source) source = -1 := by
  have hsouth : 0 < source.2.1 := by
    by_contra h
    apply hfixed
    left
    omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
    (fun d => isingNatCappedTent source.2.1 d.2.1) source = -1
  rw [faceRowFunction_laplacian_of_not_fixed n _ source hfixed]
  exact isingNatCappedTent_secondDifference_source source.2.1 hsouth

theorem faceCornerCaps_edgewise
    (n : Nat) (source x y : FKIsingSquareFullFaceNode n)
    (hxy : (fkIsingSquareFullFaceGraph n).Adj x y) :
    (faceRobinColumnCap source y - faceRobinColumnCap source x) *
        (faceBottomRowCap source y - faceBottomRowCap source x) = 0 := by
  rcases hxy with hvertical | hhorizontal
  · have hx : x.1 = y.1 := hvertical.1
    simp [faceRobinColumnCap, hx]
  · have hy : x.2 = y.2 := hhorizontal.1
    simp [faceBottomRowCap, hy]


theorem facePointPoissonBarrier_le_lowerLeftProduct
    (n : Nat) (source x : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
    (hleft : 0 < source.1.1) :
    facePointPoissonBarrier n (some source) (some x) <=
      faceRobinColumnCap source x * faceBottomRowCap source x /
        (faceRobinColumnCap source source + faceBottomRowCap source source) := by
  letI : Nonempty (FKIsingSquareFullFaceNode n) := ⟨source⟩
  have hreach : forall c : FKIsingSquareFullFaceNode n, exists b,
      (fkIsingSquareFullFaceFixedBoundary n b \/
        0 < isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) b) /\
        (fkIsingSquareFullFaceGraph n).Reachable c b := by
    intro c
    obtain ⟨b, hb, hcb⟩ := fkIsingSquareFullFace_reaches_fixed_or_ghost n c
    refine ⟨b, ?_, hcb⟩
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr ((isingFermionicGhostRate_pos_iff
        (fkIsingSquareFullFaceGhostMultiplicity n) b).2 hb)
  have hden : 0 < faceRobinColumnCap source source +
      faceBottomRowCap source source := by
    have hpos : 0 < faceRobinColumnCap source source := by
      unfold faceRobinColumnCap isingNatCappedRobinTent
      have hnonneg := isingNatCappedTent_nonneg source.1.1 source.1.1
      have hrecip : 0 < 1 / isingFermionicGhostCoefficient :=
        one_div_pos.mpr isingFermionicGhostCoefficient_pos
      linarith
    linarith [faceBottomRowCap_nonneg source source]
  change isingFiniteWeightedPointPoissonBarrier
      (isingFiniteGhostGraph (fkIsingSquareFullFaceGraph n)
        (isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n)))
      (isingFiniteGhostConductance (fkIsingSquareFullFaceGraph n)
        (isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n)))
      (isingFiniteGhostBoundaryWith
        (fkIsingSquareFullFaceFixedBoundary n))
      _ _ _ (some source) (some x) <= _
  apply isingFiniteGhostPointPoissonBarrier_le_splitProduct
    (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate
      (fkIsingSquareFullFaceGhostMultiplicity n))
    (isingFermionicGhostRate
      (fkIsingSquareFullFaceGhostMultiplicity n))
    (fun _ => 0)
    (fkIsingSquareFullFaceFixedBoundary n)
  · exact isingFermionicGhostRate_nonneg _
  · intro c
    simp
  · exact hreach
  · exact hfixed
  · exact faceRobinColumnCap_nonneg source
  · exact faceBottomRowCap_nonneg source
  · exact hden
  · exact faceCornerCaps_edgewise n source
  · intro c hc
    exact faceRobinColumnCap_modifiedLaplacian_nonpos
      n source c hleft hc
  · intro c hc
    simpa using faceBottomRowCap_laplacian_nonpos n source c hc
  · exact (faceRobinColumnCap_modifiedLaplacian_source
      n source hfixed hleft).le
  · simpa using (faceBottomRowCap_laplacian_source
      n source hfixed).le


theorem facePointPoissonBarrier_le_lowerLeftRadius
    (n radius : Nat) (distance : Real)
    (source x : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
    (hleft : 0 < source.1.1)
    (hcorner : x.1.1 + x.2.1 <= radius)
    (hdistance : 0 < distance)
    (hsourceDistance : distance <=
      (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient +
        (source.2.1 : Real)) :
    facePointPoissonBarrier n (some source) (some x) <=
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) *
        (radius : Real) / distance := by
  have hgreen := facePointPoissonBarrier_le_lowerLeftProduct
    n source x hfixed hleft
  have hcol : faceRobinColumnCap source x <=
      (radius : Real) + 1 / isingFermionicGhostCoefficient := by
    unfold faceRobinColumnCap isingNatCappedRobinTent
    have htent := isingNatCappedTent_le_coordinate source.1.1 x.1.1
    have hx : (x.1.1 : Real) <= radius := by
      exact_mod_cast (show x.1.1 <= radius by omega)
    linarith
  have hrow : faceBottomRowCap source x <= (radius : Real) := by
    unfold faceBottomRowCap
    have htent := isingNatCappedTent_le_coordinate source.2.1 x.2.1
    have hx : (x.2.1 : Real) <= radius := by
      exact_mod_cast (show x.2.1 <= radius by omega)
    exact htent.trans hx
  have hcol0 := faceRobinColumnCap_nonneg source x
  have hrow0 := faceBottomRowCap_nonneg source x
  have hbound0 : 0 <=
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) *
        (radius : Real) := by
    exact mul_nonneg
      (add_nonneg (Nat.cast_nonneg _)
        (one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le))
      (Nat.cast_nonneg _)
  have hnum : faceRobinColumnCap source x * faceBottomRowCap source x <=
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) *
        (radius : Real) :=
    mul_le_mul hcol hrow hrow0
      (add_nonneg (Nat.cast_nonneg _)
        (one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le))
  have hden : distance <=
      faceRobinColumnCap source source + faceBottomRowCap source source := by
    simpa [faceRobinColumnCap, faceBottomRowCap,
      isingNatCappedRobinTent, isingNatCappedTent_self] using
      hsourceDistance
  exact hgreen.trans (div_le_div₀ hbound0 hnum hdistance hden)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
