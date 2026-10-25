/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryAverage
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialRegularity


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareBoundaryRadialPatchFullObservableExtension_apply
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    fkIsingSquareBoundaryRadialPatchFullObservableExtension n m hn hm i j =
      fkIsingSquareBoundaryRadialPatchFullObservable
        n m hn hm ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [fkIsingSquareBoundaryRadialPatchFullObservableExtension, hi, hj]


theorem fkIsingSquareBoundaryRadialPatchFullObservable_cellCR
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi : i + 2 < m) (hj : j + 2 < m) :
    IsingCellCRAt
      (fkIsingSquareBoundaryRadialPatchFullObservableExtension n m hn hm) i j := by
  by_cases heven : Even (i + 1 + (j + 1))
  · have hquad := fkIsingSquareBoundaryRadialPatchFullObservable_quad
      n m (i + 1) (j + 1) hn hm (by omega) (by omega)
      (by omega) (by omega) heven
    unfold IsingCellCRAt
      fkIsingSquareBoundaryRadialPatchFullObservableExtension
    simp [show i < m by omega, show i + 1 < m by omega,
      show j < m by omega, show j + 1 < m by omega]
    simpa using hquad.2.2
  · have hquad := fkIsingSquareBoundaryRadialPatchFullObservable_quad_of_odd
      n m (i + 1) (j + 1) hn hm (by omega) (by omega)
      (by omega) (by omega) heven
    unfold IsingCellCRAt
      fkIsingSquareBoundaryRadialPatchFullObservableExtension
    simp [show i < m by omega, show i + 1 < m by omega,
      show j < m by omega, show j + 1 < m by omega]
    have h := hquad.2.2
    simp only [Nat.add_sub_cancel] at h
    linear_combination -h


theorem fkIsingSquareBoundaryRadialPatchFullObservable_leapfrog_harmonic
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi : i + 3 < m) (hj : j + 3 < m) :
    fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩ +
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j + 2, by omega⟩ +
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i + 2, by omega⟩ ⟨j, by omega⟩ +
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ =
      4 * fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ := by
  have hSW := fkIsingSquareBoundaryRadialPatchFullObservable_cellCR
    n m i j hn hm (by omega) (by omega)
  have hSE := fkIsingSquareBoundaryRadialPatchFullObservable_cellCR
    n m (i + 1) j hn hm (by omega) (by omega)
  have hNW := fkIsingSquareBoundaryRadialPatchFullObservable_cellCR
    n m i (j + 1) hn hm (by omega) (by omega)
  have hNE := fkIsingSquareBoundaryRadialPatchFullObservable_cellCR
    n m (i + 1) (j + 1) hn hm (by omega) (by omega)
  have h := isingCellCRAt_leapfrog_harmonic
    (fkIsingSquareBoundaryRadialPatchFullObservableExtension n m hn hm)
    i j hSW hSE hNW hNE
  simpa [fkIsingSquareBoundaryRadialPatchFullObservableExtension,
    show i < m by omega, show j < m by omega,
    show i + 1 < m by omega, show j + 1 < m by omega,
    show i + 2 < m by omega, show j + 2 < m by omega] using h


end
end StatMech.Universality
