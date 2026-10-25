/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTVRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredStoppedWalk.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredFourSectorAssembly.Part5


namespace StatMech.Universality

open Metric Set

noncomputable section

theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le_of_margin
    (n i j rho : Nat) (mesh : Real) (hn : 0 < n)
    (hi0 : 0 < i) (hi1 : i + 1 < 2 * n)
    (hj0 : 0 < j) (hj1 : j + 1 < 2 * n)
    (hrho : 0 < rho) (hmesh : 0 < mesh)
    (hiLeft : rho ≤ i - 1) (hiRight : i + rho ≤ 2 * n - 2)
    (hjBottom : rho ≤ j - 1) (hjTop : j + rho ≤ 2 * n - 2) :
    let north := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i, by omega⟩ ⟨j - 1, by omega⟩
    let east := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i, by omega⟩ ⟨j, by omega⟩
    let south := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i - 1, by omega⟩ ⟨j, by omega⟩
    let west := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    ‖north / (Real.sqrt (2 * mesh) : Complex) -
        east / (Real.sqrt (2 * mesh) : Complex)‖ ≤
          608 / ((rho : Real) * Real.sqrt (2 * mesh)) ∧
      ‖east / (Real.sqrt (2 * mesh) : Complex) -
        south / (Real.sqrt (2 * mesh) : Complex)‖ ≤
          608 / ((rho : Real) * Real.sqrt (2 * mesh)) ∧
      ‖south / (Real.sqrt (2 * mesh) : Complex) -
        west / (Real.sqrt (2 * mesh) : Complex)‖ ≤
          608 / ((rho : Real) * Real.sqrt (2 * mesh)) ∧
      ‖west / (Real.sqrt (2 * mesh) : Complex) -
        north / (Real.sqrt (2 * mesh) : Complex)‖ ≤
          608 / ((rho : Real) * Real.sqrt (2 * mesh)) := by
  let R := 2 * n - 2
  have hfit : 0 + R + 1 < 2 * n := by
    dsimp [R]
    omega
  let pN : IsingLeapfrogBox R :=
    (⟨i, by dsimp [R]; omega⟩, ⟨j - 1, by dsimp [R]; omega⟩)
  let pE : IsingLeapfrogBox R :=
    (⟨i, by dsimp [R]; omega⟩, ⟨j, by dsimp [R]; omega⟩)
  let pS : IsingLeapfrogBox R :=
    (⟨i - 1, by dsimp [R]; omega⟩, ⟨j, by dsimp [R]; omega⟩)
  let pW : IsingLeapfrogBox R :=
    (⟨i - 1, by dsimp [R]; omega⟩, ⟨j - 1, by dsimp [R]; omega⟩)
  have hmarginN : IsingLeapfrogInteriorMargin R rho pN := by
    simp only [IsingLeapfrogInteriorMargin, pN]
    dsimp [R]
    omega
  have hmarginE : IsingLeapfrogInteriorMargin R rho pE := by
    simp only [IsingLeapfrogInteriorMargin, pE]
    dsimp [R]
    omega
  have hmarginS : IsingLeapfrogInteriorMargin R rho pS := by
    simp only [IsingLeapfrogInteriorMargin, pS]
    dsimp [R]
    omega
  have hmarginW : IsingLeapfrogInteriorMargin R rho pW := by
    simp only [IsingLeapfrogInteriorMargin, pW]
    dsimp [R]
    omega
  have hNSAdj : IsingLeapfrogDiagonalAdjacent pN pS := by
    constructor
    · change i.dist (i - 1) = 1
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.sub_le i 1)]
      omega
    · change (j - 1).dist j = 1
      rw [Nat.dist_eq_sub_of_le (Nat.sub_le j 1)]
      omega
  have hEWAdj : IsingLeapfrogDiagonalAdjacent pE pW := by
    constructor
    · change i.dist (i - 1) = 1
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.sub_le i 1)]
      omega
    · change j.dist (j - 1) = 1
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.sub_le j 1)]
      omega
  have hNS :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_physicalNormalized_norm_sub_le
      n 0 0 R rho mesh hn hfit hfit hmesh pN pS hrho
      hmarginN hmarginS hNSAdj
  have hEW :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_physicalNormalized_norm_sub_le
      n 0 0 R rho mesh hn hfit hfit hmesh pE pW hrho
      hmarginE hmarginW hEWAdj
  have hedges :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le
      n i j hn hi0 hi1 hj0 hj1 (Real.sqrt (2 * mesh))
      (304 / ((rho : Real) * Real.sqrt (2 * mesh)))
      (by simpa [R, pN, pS,
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow] using hNS)
      (by simpa [R, pE, pW,
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow] using hEW)
  simpa only [show
      2 * (304 / ((rho : Real) * Real.sqrt (2 * mesh))) =
        608 / ((rho : Real) * Real.sqrt (2 * mesh)) by ring] using hedges


end
end StatMech.Universality
