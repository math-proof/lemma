/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerGreen.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem faceTopRowCap_nonneg
    (n : Nat) (source c : FKIsingSquareFullFaceNode n) :
    0 <= faceTopRowCap n source c :=
  isingNatReverseCappedTent_nonneg (2 * n - 1) source.2.1 c.2.1

theorem faceTopRowCap_laplacian_nonpos
    (n : Nat) (source c : FKIsingSquareFullFaceNode n)
    (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (faceTopRowCap n source) c <= 0 := by
  have hsouth : 0 < c.2.1 := by
    by_contra h
    apply hc
    left
    omega
  have hnorth : c.2.1 < 2 * n - 1 := by
    by_contra h
    apply hc
    right
    right
    have hcBound := c.2.isLt
    omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
    (fun d => isingNatReverseCappedTent
      (2 * n - 1) source.2.1 d.2.1) c <= 0
  rw [faceRowFunction_laplacian_of_not_fixed n _ c hc]
  exact isingNatReverseCappedTent_secondDifference_nonpos
    (2 * n - 1) source.2.1 c.2.1 hsouth hnorth

theorem faceTopRowCap_laplacian_source
    (n : Nat) (source : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source)) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (faceTopRowCap n source) source = -1 := by
  have hsouth : 0 < source.2.1 := by
    by_contra h
    apply hfixed
    left
    omega
  have hnorth : source.2.1 < 2 * n - 1 := by
    by_contra h
    apply hfixed
    right
    right
    have hcBound := source.2.isLt
    omega
  change isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
    (fun d => isingNatReverseCappedTent
      (2 * n - 1) source.2.1 d.2.1) source = -1
  rw [faceRowFunction_laplacian_of_not_fixed n _ source hfixed]
  exact isingNatReverseCappedTent_secondDifference_source
    (2 * n - 1) source.2.1 hsouth hnorth

theorem faceUpperCornerCaps_edgewise
    (n : Nat) (source x y : FKIsingSquareFullFaceNode n)
    (hxy : (fkIsingSquareFullFaceGraph n).Adj x y) :
    (faceRobinColumnCap source y - faceRobinColumnCap source x) *
        (faceTopRowCap n source y - faceTopRowCap n source x) = 0 := by
  rcases hxy with hvertical | hhorizontal
  · have hx : x.1 = y.1 := hvertical.1
    simp [faceRobinColumnCap, hx]
  · have hy : x.2 = y.2 := hhorizontal.1
    simp [faceTopRowCap, hy]


theorem facePointPoissonBarrier_le_upperLeftProduct
    (n : Nat) (source x : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
    (hleft : 0 < source.1.1) :
    facePointPoissonBarrier n (some source) (some x) <=
      faceRobinColumnCap source x * faceTopRowCap n source x /
        (faceRobinColumnCap source source + faceTopRowCap n source source) := by
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
      faceTopRowCap n source source := by
    have hpos : 0 < faceRobinColumnCap source source := by
      unfold faceRobinColumnCap isingNatCappedRobinTent
      have hnonneg := isingNatCappedTent_nonneg source.1.1 source.1.1
      have hrecip : 0 < 1 / isingFermionicGhostCoefficient :=
        one_div_pos.mpr isingFermionicGhostCoefficient_pos
      linarith
    linarith [faceTopRowCap_nonneg n source source]
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
  · exact faceTopRowCap_nonneg n source
  · exact hden
  · exact faceUpperCornerCaps_edgewise n source
  · intro c hc
    exact faceRobinColumnCap_modifiedLaplacian_nonpos
      n source c hleft hc
  · intro c hc
    simpa using faceTopRowCap_laplacian_nonpos n source c hc
  · exact (faceRobinColumnCap_modifiedLaplacian_source
      n source hfixed hleft).le
  · simpa using (faceTopRowCap_laplacian_source
      n source hfixed).le


theorem facePointPoissonBarrier_le_upperLeftRadius
    (n radius : Nat) (distance : Real)
    (source x : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
    (hleft : 0 < source.1.1)
    (hcorner : x.1.1 + (2 * n - 1 - x.2.1) <= radius)
    (hdistance : 0 < distance)
    (hsourceDistance : distance <=
      (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient +
        (2 * n - 1 - source.2.1 : Nat)) :
    facePointPoissonBarrier n (some source) (some x) <=
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) *
        (radius : Real) / distance := by
  have hgreen := facePointPoissonBarrier_le_upperLeftProduct
    n source x hfixed hleft
  have hcol : faceRobinColumnCap source x <=
      (radius : Real) + 1 / isingFermionicGhostCoefficient := by
    unfold faceRobinColumnCap isingNatCappedRobinTent
    have htent := isingNatCappedTent_le_coordinate source.1.1 x.1.1
    have hx : (x.1.1 : Real) <= radius := by
      exact_mod_cast (show x.1.1 <= radius by omega)
    linarith
  have hrow : faceTopRowCap n source x <= (radius : Real) := by
    unfold faceTopRowCap
    have htent := isingNatReverseCappedTent_le_coordinate
      (2 * n - 1) source.2.1 x.2.1
    have hx : ((2 * n - 1 - x.2.1 : Nat) : Real) <= radius := by
      exact_mod_cast (show 2 * n - 1 - x.2.1 <= radius by omega)
    exact htent.trans hx
  have hrow0 := faceTopRowCap_nonneg n source x
  have hbound0 : 0 <=
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) *
        (radius : Real) := by
    exact mul_nonneg
      (add_nonneg (Nat.cast_nonneg _)
        (one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le))
      (Nat.cast_nonneg _)
  have hnum : faceRobinColumnCap source x * faceTopRowCap n source x <=
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) *
        (radius : Real) :=
    mul_le_mul hcol hrow hrow0
      (add_nonneg (Nat.cast_nonneg _)
        (one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le))
  have hden : distance <=
      faceRobinColumnCap source source + faceTopRowCap n source source := by
    simpa [faceRobinColumnCap, faceTopRowCap,
      isingNatCappedRobinTent, isingNatCappedTent_self,
      isingNatReverseCappedTent_self] using hsourceDistance
  exact hgreen.trans (div_le_div₀ hbound0 hnum hdistance hden)


theorem facePointPoissonBarrier_le_markedEndpointRadius
    (n radius : Nat) (distance : Real)
    (source x : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
    (hleft : 0 < source.1.1)
    (hx : faceMarkedEndpointLayer n radius (some x))
    (hdistance : 0 < distance)
    (hlowerDistance : distance <=
      (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient +
        (source.2.1 : Real))
    (hupperDistance : distance <=
      (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient +
        (2 * n - 1 - source.2.1 : Nat)) :
    facePointPoissonBarrier n (some source) (some x) <=
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) *
        (radius : Real) / distance := by
  rcases faceMarkedEndpointLayer_coordinate_cases n radius x hx with
    hlower | hupper
  · exact facePointPoissonBarrier_le_lowerLeftRadius
      n radius distance source x hfixed hleft hlower hdistance hlowerDistance
  · exact facePointPoissonBarrier_le_upperLeftRadius
      n radius distance source x hfixed hleft hupper hdistance hupperDistance


theorem facePointPoissonBarrier_le_exceptionalSourceRadius
    (n radius : Nat) (distance : Real)
    (source : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
    (hleft : 0 < source.1.1)
    (hdistance : 0 < distance)
    (hlowerDistance : distance <=
      (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient +
        (source.2.1 : Real))
    (hupperDistance : distance <=
      (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient +
        (2 * n - 1 - source.2.1 : Nat)) :
    forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources
        (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius) ->
      facePointPoissonBarrier n (some source) z <=
        ((radius : Real) + 1 / isingFermionicGhostCoefficient) *
          (radius : Real) / distance := by
  intro z hz
  have hmarked : faceMarkedEndpointLayer n radius z := by
    have hz' : Not (faceDirichletBoundary n z) /\
        faceMarkedEndpointLayer n radius z := by
      simpa [isingFiniteWeightedInteriorExceptionalSources] using hz
    exact hz'.2
  cases z with
  | none => exact False.elim hmarked
  | some x =>
      exact facePointPoissonBarrier_le_markedEndpointRadius
        n radius distance source x hfixed hleft hmarked hdistance
        hlowerDistance hupperDistance

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
