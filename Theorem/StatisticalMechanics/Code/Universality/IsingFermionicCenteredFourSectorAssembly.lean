/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredNESectorRate


namespace StatMech.Universality

noncomputable section

theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le
    (n i j : Nat) (hn : 0 < n)
    (hi0 : 0 < i) (hi1 : i + 1 < 2 * n)
    (hj0 : 0 < j) (hj1 : j + 1 < 2 * n) (r delta : Real)
    (hNS : ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i - 1, by omega⟩ ⟨j, by omega⟩ / (r : Complex)‖ ≤ delta)
    (hEW : ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i, by omega⟩ ⟨j, by omega⟩ / (r : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex)‖ ≤ delta) :
    let north := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i, by omega⟩ ⟨j - 1, by omega⟩
    let east := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i, by omega⟩ ⟨j, by omega⟩
    let south := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i - 1, by omega⟩ ⟨j, by omega⟩
    let west := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    ‖north / (r : Complex) - east / (r : Complex)‖ ≤ 2 * delta ∧
      ‖east / (r : Complex) - south / (r : Complex)‖ ≤ 2 * delta ∧
      ‖south / (r : Complex) - west / (r : Complex)‖ ≤ 2 * delta ∧
      ‖west / (r : Complex) - north / (r : Complex)‖ ≤ 2 * delta := by
  dsimp only
  by_cases heven : Even (i + j)
  · have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad
        n i j hn hi0 hi1 hj0 hj1 heven)
    exact projectionCycle_crossParity_norm_div_sub_div_le _ _ _ _ r delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hNS hEW
  · have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd
        n i j hn hi0 hi1 hj0 hj1 heven)
    have hSN := hNS
    have hWE := hEW
    rw [norm_sub_rev] at hSN hWE
    have hodd := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ r delta hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2
      hSN hWE
    exact ⟨hodd.2.2.1, hodd.2.2.2, hodd.1, hodd.2.1⟩


end
end StatMech.Universality
