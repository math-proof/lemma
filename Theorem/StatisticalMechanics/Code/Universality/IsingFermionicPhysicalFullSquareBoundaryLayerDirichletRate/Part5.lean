/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part5


namespace StatMech.Universality

open Filter Finset Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem faceRowPoissonBarrier_nonneg
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    0 ≤ faceRowPoissonBarrier n c := by
  have hc : (c.2.1 : Real) ≤ 2 * (n : Real) := by
    exact_mod_cast (Nat.le_of_lt c.2.isLt)
  unfold faceRowPoissonBarrier
  positivity

theorem faceRowPoissonBarrier_le
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    faceRowPoissonBarrier n c ≤ faceExplicitPoissonBarrierBound n := by
  unfold faceRowPoissonBarrier faceExplicitPoissonBarrierBound
  nlinarith [sq_nonneg ((c.2.1 : Real) - (n : Real))]

theorem faceExplicitPoissonBarrier_nonneg (n : Nat) :
    ∀ c, 0 ≤ faceExplicitPoissonBarrier n c := by
  intro c
  cases c with
  | none => simp [faceExplicitPoissonBarrier]
  | some c => exact faceRowPoissonBarrier_nonneg n c

theorem faceExplicitPoissonBarrier_le_bound (n : Nat) :
    ∀ c, faceExplicitPoissonBarrier n c ≤
      faceExplicitPoissonBarrierBound n := by
  intro c
  cases c with
  | none =>
      simp [faceExplicitPoissonBarrier]
      exact div_nonneg (sq_nonneg (n : Real)) (by norm_num)
  | some c => exact faceRowPoissonBarrier_le n c


theorem face_neighborFinset_left
    (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (hleft : c.1.1 = 0)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hsouth : 0 < c.2.1)
    [Fintype ↑((fkIsingSquareFullFaceGraph n).neighborSet c)] :
    (fkIsingSquareFullFaceGraph n).neighborFinset c =
      {faceEastNeighbor n c heast, faceNorthNeighbor n c hnorth,
        faceSouthNeighbor n c hsouth} := by
  ext y
  rw [SimpleGraph.mem_neighborFinset]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨hcol, hup | hdown⟩ | ⟨hrow, hright | hwest⟩)
    · right; left
      apply Prod.ext
      · exact hcol.symm
      · apply Fin.ext
        simp [faceNorthNeighbor]
        omega
    · right; right
      apply Prod.ext
      · exact hcol.symm
      · apply Fin.ext
        simp [faceSouthNeighbor]
        omega
    · left
      apply Prod.ext
      · apply Fin.ext
        simp [faceEastNeighbor]
        omega
      · exact hrow.symm
    · have hy := y.1.2
      omega
  · rintro (rfl | rfl | rfl)
    · exact Or.inr ⟨rfl, Or.inl (by simp [faceEastNeighbor])⟩
    · exact Or.inl ⟨rfl, Or.inl (by simp [faceNorthNeighbor])⟩
    · exact Or.inl ⟨rfl, Or.inr (by simp [faceSouthNeighbor]; omega)⟩


theorem faceColumnFunction_laplacian_of_not_fixed
    (n : Nat) (F : Nat -> Real) (c : FKIsingSquareFullFaceNode n)
    (hc : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => F d.1.1) c =
      if c.1.1 = 0 then F 1 - F 0
      else F (c.1.1 + 1) + F (c.1.1 - 1) - 2 * F c.1.1 := by
  classical
  have hsouth : 0 < c.2.1 := by
    by_contra h
    apply hc
    left
    omega
  have heast : c.1.1 + 1 < 2 * n := by
    by_contra h
    apply hc
    right
    left
    omega
  have hnorth : c.2.1 + 1 < 2 * n := by
    by_contra h
    apply hc
    right
    right
    omega
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cS := faceSouthNeighbor n c hsouth
  have hEN : cE ≠ cN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
    simp [cE, cN, faceEastNeighbor, faceNorthNeighbor] at h0
  have hES : cE ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
    simp [cE, cS, faceEastNeighbor, faceSouthNeighbor] at h0
  have hNS : cN ≠ cS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
    simp [cN, cS, faceNorthNeighbor, faceSouthNeighbor] at h1
    omega
  by_cases hleft : c.1.1 = 0
  · unfold isingFiniteGraphLaplacian
    rw [show (fkIsingSquareFullFaceGraph n).neighborFinset c =
        {cE, cN, cS} by
      exact face_neighborFinset_left n c hleft heast hnorth hsouth]
    have he_not : cE ∉ ({cN, cS} : Finset _) := by simp [hEN, hES]
    have hn_not : cN ∉ ({cS} : Finset _) := by simp [hNS]
    rw [Finset.sum_insert he_not, Finset.sum_insert hn_not,
      Finset.sum_singleton]
    simp [cE, cN, cS, faceEastNeighbor, faceNorthNeighbor,
      faceSouthNeighbor, hleft]
  · let cW := faceWestNeighbor n c (by omega)
    have hEW : cE ≠ cW := by
      intro h
      have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
      simp [cE, cW, faceEastNeighbor, faceWestNeighbor] at h0
      omega
    have hNW : cN ≠ cW := by
      intro h
      have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
      simp [cN, cW, faceNorthNeighbor, faceWestNeighbor] at h1
    have hWS : cW ≠ cS := by
      intro h
      have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
      simp [cW, cS, faceWestNeighbor, faceSouthNeighbor] at h1
      omega
    unfold isingFiniteGraphLaplacian
    rw [show (fkIsingSquareFullFaceGraph n).neighborFinset c =
        {cE, cN, cW, cS} by
      exact fkIsingSquareBoundaryFullFace_neighborFinset n c heast hnorth
        (by omega) hsouth]
    have he_not : cE ∉ ({cN, cW, cS} : Finset _) := by
      simp [hEN, hEW, hES]
    have hn_not : cN ∉ ({cW, cS} : Finset _) := by simp [hNW, hNS]
    have hw_not : cW ∉ ({cS} : Finset _) := by simp [hWS]
    rw [Finset.sum_insert he_not, Finset.sum_insert hn_not,
      Finset.sum_insert hw_not, Finset.sum_singleton]
    simp [cE, cN, cW, cS, faceEastNeighbor, faceNorthNeighbor,
      faceWestNeighbor, faceSouthNeighbor, hleft]
    ring


theorem faceRowFunction_laplacian_of_not_fixed
    (n : Nat) (F : Nat -> Real) (c : FKIsingSquareFullFaceNode n)
    (hc : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => F d.2.1) c =
      F (c.2.1 + 1) + F (c.2.1 - 1) - 2 * F c.2.1 := by
  classical
  have hsouth : 0 < c.2.1 := by
    by_contra h
    apply hc
    left
    omega
  have heast : c.1.1 + 1 < 2 * n := by
    by_contra h
    apply hc
    right
    left
    omega
  have hnorth : c.2.1 + 1 < 2 * n := by
    by_contra h
    apply hc
    right
    right
    omega
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cS := faceSouthNeighbor n c hsouth
  have hEN : cE ≠ cN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
    simp [cE, cN, faceEastNeighbor, faceNorthNeighbor] at h0
  have hES : cE ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
    simp [cE, cS, faceEastNeighbor, faceSouthNeighbor] at h0
  have hNS : cN ≠ cS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
    simp [cN, cS, faceNorthNeighbor, faceSouthNeighbor] at h1
    omega
  by_cases hleft : c.1.1 = 0
  · unfold isingFiniteGraphLaplacian
    rw [show (fkIsingSquareFullFaceGraph n).neighborFinset c =
        {cE, cN, cS} by
      exact face_neighborFinset_left n c hleft heast hnorth hsouth]
    have he_not : cE ∉ ({cN, cS} : Finset _) := by simp [hEN, hES]
    have hn_not : cN ∉ ({cS} : Finset _) := by simp [hNS]
    rw [Finset.sum_insert he_not, Finset.sum_insert hn_not,
      Finset.sum_singleton]
    simp [cE, cN, cS, faceEastNeighbor, faceNorthNeighbor,
      faceSouthNeighbor]
    ring
  · let cW := faceWestNeighbor n c (by omega)
    have hEW : cE ≠ cW := by
      intro h
      have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
      simp [cE, cW, faceEastNeighbor, faceWestNeighbor] at h0
      omega
    have hNW : cN ≠ cW := by
      intro h
      have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
      simp [cN, cW, faceNorthNeighbor, faceWestNeighbor] at h1
    have hWS : cW ≠ cS := by
      intro h
      have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
      simp [cW, cS, faceWestNeighbor, faceSouthNeighbor] at h1
      omega
    unfold isingFiniteGraphLaplacian
    rw [show (fkIsingSquareFullFaceGraph n).neighborFinset c =
        {cE, cN, cW, cS} by
      exact fkIsingSquareBoundaryFullFace_neighborFinset n c heast hnorth
        (by omega) hsouth]
    have he_not : cE ∉ ({cN, cW, cS} : Finset _) := by
      simp [hEN, hEW, hES]
    have hn_not : cN ∉ ({cW, cS} : Finset _) := by simp [hNW, hNS]
    have hw_not : cW ∉ ({cS} : Finset _) := by simp [hWS]
    rw [Finset.sum_insert he_not, Finset.sum_insert hn_not,
      Finset.sum_insert hw_not, Finset.sum_singleton]
    simp [cE, cN, cW, cS, faceEastNeighbor, faceNorthNeighbor,
      faceWestNeighbor, faceSouthNeighbor]
    ring

theorem faceRowPoissonBarrier_laplacian
    (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (hc : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (faceRowPoissonBarrier n) c = -1 := by
  classical
  have hsouth : 0 < c.2.1 := by
    by_contra h
    apply hc
    left
    omega
  have heast : c.1.1 + 1 < 2 * n := by
    have hcBound := c.1.isLt
    by_contra h
    apply hc
    right
    left
    omega
  have hnorth : c.2.1 + 1 < 2 * n := by
    have hcBound := c.2.isLt
    by_contra h
    apply hc
    right
    right
    omega
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cS := faceSouthNeighbor n c hsouth
  have hEN : cE ≠ cN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cN, faceEastNeighbor, faceNorthNeighbor] at h0
  have hES : cE ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cS, faceEastNeighbor, faceSouthNeighbor] at h0
  have hNS : cN ≠ cS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.2.1) h
    simp [cN, cS, faceNorthNeighbor, faceSouthNeighbor] at h1
    omega
  have hcast : ((c.2.1 - 1 : Nat) : Real) = (c.2.1 : Real) - 1 := by
    rw [Nat.cast_sub (R := Real) (by omega : 1 ≤ c.2.1)]
    norm_num
  by_cases hleft : c.1.1 = 0
  · unfold isingFiniteGraphLaplacian
    rw [show (fkIsingSquareFullFaceGraph n).neighborFinset c =
        {cE, cN, cS} by
      exact face_neighborFinset_left n c hleft heast hnorth hsouth]
    have he_not : cE ∉ ({cN, cS} : Finset _) := by simp [hEN, hES]
    have hn_not : cN ∉ ({cS} : Finset _) := by simp [hNS]
    rw [Finset.sum_insert he_not, Finset.sum_insert hn_not,
      Finset.sum_singleton]
    simp [cE, cN, cS, faceRowPoissonBarrier,
      faceEastNeighbor, faceNorthNeighbor, faceSouthNeighbor]
    rw [hcast]
    ring
  · let cW := faceWestNeighbor n c (by omega)
    have hEW : cE ≠ cW := by
      intro h
      have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
      simp [cE, cW, faceEastNeighbor, faceWestNeighbor] at h0
      omega
    have hNW : cN ≠ cW := by
      intro h
      have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.2.1) h
      simp [cN, cW, faceNorthNeighbor, faceWestNeighbor] at h1
    have hWS : cW ≠ cS := by
      intro h
      have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.2.1) h
      simp [cW, cS, faceWestNeighbor, faceSouthNeighbor] at h1
      omega
    unfold isingFiniteGraphLaplacian
    rw [show (fkIsingSquareFullFaceGraph n).neighborFinset c =
        {cE, cN, cW, cS} by
      exact fkIsingSquareBoundaryFullFace_neighborFinset n c heast hnorth
        (by omega) hsouth]
    have he_not : cE ∉ ({cN, cW, cS} : Finset _) := by
      simp [hEN, hEW, hES]
    have hn_not : cN ∉ ({cW, cS} : Finset _) := by simp [hNW, hNS]
    have hw_not : cW ∉ ({cS} : Finset _) := by simp [hWS]
    rw [Finset.sum_insert he_not, Finset.sum_insert hn_not,
      Finset.sum_insert hw_not, Finset.sum_singleton]
    simp [cE, cN, cW, cS,
      faceRowPoissonBarrier, faceEastNeighbor, faceNorthNeighbor,
      faceWestNeighbor, faceSouthNeighbor]
    rw [hcast]
    ring

theorem faceExplicitPoissonBarrier_laplacian
    (n : Nat) (c : Option (FKIsingSquareFullFaceNode n))
    (hc : ¬ faceDirichletBoundary n c) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
      (faceExplicitPoissonBarrier n) c ≤ -1 := by
  cases c with
  | none => exact False.elim (hc trivial)
  | some c =>
      change ¬ fkIsingSquareFullFaceFixedBoundary n c at hc
      have hbarrier : faceExplicitPoissonBarrier n =
          isingFiniteGhostExtension 0 (faceRowPoissonBarrier n) := by
        funext z
        cases z <;> rfl
      change isingFiniteWeightedLaplacian
        (isingFiniteGhostConductance (fkIsingSquareFullFaceGraph n)
          (isingFermionicGhostRate
            (fkIsingSquareFullFaceGhostMultiplicity n)))
        (faceExplicitPoissonBarrier n) (some c) ≤ -1
      rw [hbarrier, isingFiniteGhostLaplacian_some,
        faceRowPoissonBarrier_laplacian n c hc]
      have hrate : 0 ≤ isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c :=
        isingFermionicGhostRate_nonneg
          (fkIsingSquareFullFaceGhostMultiplicity n) c
      have hrow := faceRowPoissonBarrier_nonneg n c
      nlinarith

theorem facePoissonBarrier_le_explicit (n : Nat) : ∀ c,
    isingFiniteWeightedPoissonBarrier
        (faceGhostGraph n) (faceGhostConductance n)
        (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
        (faceGhostConductance_pos_of_adj n)
        (faceGhost_reaches_boundary n) c ≤
      faceExplicitPoissonBarrier n c := by
  apply isingFiniteWeighted_laplacian_comparison
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n)
    (isingFiniteWeightedPoissonBarrier
      (faceGhostGraph n) (faceGhostConductance n)
      (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
      (faceGhostConductance_pos_of_adj n)
      (faceGhost_reaches_boundary n))
    (faceExplicitPoissonBarrier n)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)
  · intro c hc
    rw [isingFiniteWeightedPoissonBarrier_boundary
      (faceGhostGraph n) (faceGhostConductance n)
      (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
      (faceGhostConductance_pos_of_adj n)
      (faceGhost_reaches_boundary n) c hc]
    exact faceExplicitPoissonBarrier_nonneg n c
  · intro c hc
    rw [isingFiniteWeightedPoissonBarrier_laplacian
      (faceGhostGraph n) (faceGhostConductance n)
      (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
      (faceGhostConductance_pos_of_adj n)
      (faceGhost_reaches_boundary n) c hc]
    exact faceExplicitPoissonBarrier_laplacian n c hc

theorem facePoissonBarrierBound_le_explicit (n : Nat) :
    facePoissonBarrierBound n ≤ faceExplicitPoissonBarrierBound n := by
  unfold facePoissonBarrierBound isingFiniteWeightedPoissonBarrierBound
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hz
  exact (facePoissonBarrier_le_explicit n c).trans
    (faceExplicitPoissonBarrier_le_bound n c)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
