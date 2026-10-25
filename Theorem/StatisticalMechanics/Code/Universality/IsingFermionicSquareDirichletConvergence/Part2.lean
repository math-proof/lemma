/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareDirichletConvergence.Part2
open Finset SimpleGraph Filter Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquare_intCast_sq_le_nat_sq
    (z : Int) (n : Nat) (h : z.natAbs ≤ n) :
    (z : Real) ^ 2 ≤ (n : Real) ^ 2 := by
  have hc : (z.natAbs : Real) ≤ (n : Real) := by
    exact_mod_cast h
  have habs : |(z : Real)| ≤ (n : Real) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hc
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg (z : Real)) (Nat.cast_nonneg n)).2 habs


theorem fkIsingSquareBoxQuadraticBarrier_laplacian
    (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hx : ¬ fkIsingSquareBoxBoundary n x) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxQuadraticBarrier n) x = -1 := by
  classical
  have hinterior (k : Fin 2) : (x.1 k).natAbs < n := by
    have hle := x.2 k
    have hne : (x.1 k).natAbs ≠ n := by
      intro heq
      exact hx ⟨k, heq⟩
    omega
  have heSite : shift 2 x.1 0 1 ∈ box 2 n := by
    intro k
    fin_cases k
    · change (x.1 0 + 1).natAbs ≤ n
      have htri := Int.natAbs_add_le (x.1 0) 1
      norm_num at htri
      have hi := hinterior 0
      omega
    · simpa [shift] using x.2 1
  have hwSite : shift 2 x.1 0 (-1) ∈ box 2 n := by
    intro k
    fin_cases k
    · change (x.1 0 + (-1)).natAbs ≤ n
      have htri := Int.natAbs_add_le (x.1 0) (-1)
      norm_num at htri
      have hi := hinterior 0
      omega
    · simpa [shift] using x.2 1
  have huSite : shift 2 x.1 1 1 ∈ box 2 n := by
    intro k
    fin_cases k
    · simpa [shift] using x.2 0
    · change (x.1 1 + 1).natAbs ≤ n
      have htri := Int.natAbs_add_le (x.1 1) 1
      norm_num at htri
      have hi := hinterior 1
      omega
  have hdSite : shift 2 x.1 1 (-1) ∈ box 2 n := by
    intro k
    fin_cases k
    · simpa [shift] using x.2 0
    · change (x.1 1 + (-1)).natAbs ≤ n
      have htri := Int.natAbs_add_le (x.1 1) (-1)
      norm_num at htri
      have hi := hinterior 1
      omega
  let e : (fkSquareBoxPlanar n).V := ⟨shift 2 x.1 0 1, heSite⟩
  let w : (fkSquareBoxPlanar n).V := ⟨shift 2 x.1 0 (-1), hwSite⟩
  let u : (fkSquareBoxPlanar n).V := ⟨shift 2 x.1 1 1, huSite⟩
  let d : (fkSquareBoxPlanar n).V := ⟨shift 2 x.1 1 (-1), hdSite⟩
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset x =
      {e, w, u, d} := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    change NearestNeighbour 2 x.1 y.1 ↔
      y = e ∨ y = w ∨ y = u ∨ y = d
    rw [nearestNeighbour_iff_shift]
    constructor
    · rintro ⟨k, s, hs, hys⟩
      fin_cases k <;> rcases hs with rfl | rfl
      · left
        apply Subtype.ext
        simpa [e] using hys
      · right; left
        apply Subtype.ext
        simpa [w] using hys
      · right; right; left
        apply Subtype.ext
        simpa [u] using hys
      · right; right; right
        apply Subtype.ext
        simpa [d] using hys
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, 1, Or.inl rfl, rfl⟩
      · exact ⟨0, -1, Or.inr rfl, rfl⟩
      · exact ⟨1, 1, Or.inl rfl, rfl⟩
      · exact ⟨1, -1, Or.inr rfl, rfl⟩
  have hew : e ≠ w := by
    intro h
    have hk := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [e, w, shift] at hk
  have heu : e ≠ u := by
    intro h
    have hk := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [e, u, shift] at hk
  have hed : e ≠ d := by
    intro h
    have hk := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [e, d, shift] at hk
  have hwu : w ≠ u := by
    intro h
    have hk := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [w, u, shift] at hk
  have hwd : w ≠ d := by
    intro h
    have hk := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [w, d, shift] at hk
  have hud : u ≠ d := by
    intro h
    have hk := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 1) h
    simp [u, d, shift] at hk
  have he_not : e ∉ ({w, u, d} : Finset (fkSquareBoxPlanar n).V) := by
    simp [hew, heu, hed]
  have hw_not : w ∉ ({u, d} : Finset (fkSquareBoxPlanar n).V) := by
    simp [hwu, hwd]
  have hu_not : u ∉ ({d} : Finset (fkSquareBoxPlanar n).V) := by
    simp [hud]
  unfold isingFiniteGraphLaplacian
  rw [hneighbors]
  rw [Finset.sum_insert he_not, Finset.sum_insert hw_not,
    Finset.sum_insert hu_not, Finset.sum_singleton]
  simp [fkIsingSquareBoxQuadraticBarrier, e, w, u, d, shift]
  ring

theorem fkIsingSquareBoxQuadraticBarrier_nonneg
    (n : Nat) (x : (fkSquareBoxPlanar n).V) :
    0 ≤ fkIsingSquareBoxQuadraticBarrier n x := by
  have h0 := fkIsingSquare_intCast_sq_le_nat_sq (x.1 0) n (x.2 0)
  have h1 := fkIsingSquare_intCast_sq_le_nat_sq (x.1 1) n (x.2 1)
  unfold fkIsingSquareBoxQuadraticBarrier
  nlinarith

theorem fkIsingSquareBoxQuadraticBarrier_le
    (n : Nat) (x : (fkSquareBoxPlanar n).V) :
    fkIsingSquareBoxQuadraticBarrier n x ≤ (n : Real) ^ 2 / 2 := by
  have h0 : 0 ≤ (x.1 0 : Real) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (x.1 1 : Real) ^ 2 := sq_nonneg _
  unfold fkIsingSquareBoxQuadraticBarrier
  nlinarith

end
end StatMech.Universality
