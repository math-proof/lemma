/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCheckerboard


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatchPrimalGraph_laplacian_eq_diagonal
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    isingFiniteGraphLaplacian (fkIsingSquareRadialPatchPrimalGraph n m hm)
        (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base)
        ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), heven⟩ =
      fkIsingSquareRadialPatchDiagonalLaplacian
        (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
  classical
  let c : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), heven⟩
  let ne : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i + 1, hi1⟩, ⟨j + 1, hj1⟩), by
      change Even ((i + 1) + (j + 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let nw : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i + 1, hi1⟩, ⟨j - 1, by omega⟩), by
      change Even ((i + 1) + (j - 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let sw : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i - 1, by omega⟩, ⟨j - 1, by omega⟩), by
      change Even ((i - 1) + (j - 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let se : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i - 1, by omega⟩, ⟨j + 1, hj1⟩), by
      change Even ((i - 1) + (j + 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  have hneighbors :
      (fkIsingSquareRadialPatchPrimalGraph n m hm).neighborFinset c =
        {ne, nw, sw, se} := by
    ext q
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton, fkIsingSquareRadialPatchPrimalGraph,
      SimpleGraph.comap_adj]
    change (fkSquareBoxPlanar n).G.Adj
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩)
        (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q) ↔ _
    rw [fkIsingSquareRadialPatch_adj_iff_diagonal
      n m i j hm hi0 hi1 hj0 hj1 heven]
    let embed := fkIsingSquareRadialPatchPrimalNodeVertex n m hm
    have hinj := fkIsingSquareRadialPatchPrimalNodeVertex_injective n m hm
    change (embed q = embed ne ∨ embed q = embed nw ∨
      embed q = embed sw ∨ embed q = embed se) ↔
      q = ne ∨ q = nw ∨ q = sw ∨ q = se
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl (hinj h)
      · exact Or.inr (Or.inl (hinj h))
      · exact Or.inr (Or.inr (Or.inl (hinj h)))
      · exact Or.inr (Or.inr (Or.inr (hinj h)))
    · rintro (rfl | rfl | rfl | rfl) <;> simp
  have hne_nw : ne ≠ nw := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m ↦ p.1.2.1) h
    simp [ne, nw] at hk
    omega
  have hne_sw : ne ≠ sw := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m ↦ p.1.1.1) h
    simp [ne, sw] at hk
    omega
  have hne_se : ne ≠ se := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m ↦ p.1.1.1) h
    simp [ne, se] at hk
    omega
  have hnw_sw : nw ≠ sw := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m ↦ p.1.1.1) h
    simp [nw, sw] at hk
    omega
  have hnw_se : nw ≠ se := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m ↦ p.1.1.1) h
    simp [nw, se] at hk
    omega
  have hsw_se : sw ≠ se := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m ↦ p.1.2.1) h
    simp [sw, se] at hk
  rw [show (⟨(⟨i, by omega⟩, ⟨j, by omega⟩), heven⟩ :
      FKIsingSquareRadialPatchPrimalNode m) = c by rfl]
  unfold isingFiniteGraphLaplacian
  rw [hneighbors]
  simp [hne_nw, hne_sw, hne_se, hnw_sw, hnw_se, hsw_se,
    fkIsingSquareRadialPatchPrimalValue, ne, nw, sw, se]
  unfold fkIsingSquareRadialPatchDiagonalLaplacian
  ring


theorem fkIsingSquareRadialPatchPrimalValue_superharmonicOn
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) :
    IsingFiniteGraphSuperharmonicOn
      (fkIsingSquareRadialPatchPrimalGraph n m hm)
      (fkIsingSquareRadialPatchPrimalBoundary m)
      (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base) := by
  intro p hp
  have hi0 : 0 < p.1.1.1 := by
    by_contra h
    apply hp
    left
    omega
  have hi1 : p.1.1.1 + 1 < m := by
    have hi := p.1.1.2
    by_contra h
    apply hp
    right; left
    omega
  have hj0 : 0 < p.1.2.1 := by
    by_contra h
    apply hp
    right; right; left
    omega
  have hj1 : p.1.2.1 + 1 < m := by
    have hj := p.1.2.2
    by_contra h
    apply hp
    right; right; right
    omega
  rw [fkIsingSquareRadialPatchPrimalGraph_laplacian_eq_diagonal
    n m p.1.1.1 p.1.2.1 hn hm hmpos base hi0 hi1 hj0 hj1 p.2]
  rw [fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_divergence
      n m p.1.1.1 p.1.2.1 hn hm hmpos hi0 hi1 hj0 hj1 p.2,
    fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_primitiveLaplacian
      n m p.1.1.1 p.1.2.1 hn hm hmpos hi0 hi1 hj0 hj1 p.2]
  apply isingPrimalPrimitiveLaplacian_nonpos_of_rotated_quad
  exact fkIsingSquareRadialPatchFullObservable_quad
    n m p.1.1.1 p.1.2.1 hn hm hi0 hi1 hj0 hj1 p.2


end
end StatMech.Universality
