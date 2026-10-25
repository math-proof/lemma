/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryAverage
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialRegularity.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryRadialPatchFullObservableWindow_harmonic
    (n m baseI baseJ R : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    IsingLeapfrogHarmonicOnBox R
      (fkIsingSquareBoundaryRadialPatchFullObservableWindow
        n m baseI baseJ R hn hm hfitI hfitJ) := by
  intro p hp
  have hx0 : 0 < p.1.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hy0 : 0 < p.2.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hxR : p.1.1 + 1 < R + 1 := by
    have hxle := p.1.2
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hyR : p.2.1 + 1 < R + 1 := by
    have hyle := p.2.2
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hphysical :=
    fkIsingSquareBoundaryRadialPatchFullObservable_leapfrog_harmonic
      n m (baseI + p.1.1 - 1) (baseJ + p.2.1 - 1) hn hm
      (by omega) (by omega)
  have hSW :
      fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogSW R p) =
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1, by omega⟩
          ⟨baseJ + p.2.1 - 1, by omega⟩ := by
    unfold fkIsingSquareBoundaryRadialPatchFullObservableWindow
      isingLeapfrogSW isingLeapfrogWest isingLeapfrogSouth
    congr 2 <;> simp only <;> omega
  have hNW :
      fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogNW R p hp) =
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 2, by omega⟩ := by
    unfold fkIsingSquareBoundaryRadialPatchFullObservableWindow
      isingLeapfrogNW isingLeapfrogWest isingLeapfrogNorth
    congr 2 <;> simp only <;> omega
  have hSE :
      fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogSE R p hp) =
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1 + 2, by omega⟩
          ⟨baseJ + p.2.1 - 1, by omega⟩ := by
    unfold fkIsingSquareBoundaryRadialPatchFullObservableWindow
      isingLeapfrogSE isingLeapfrogEast isingLeapfrogSouth
    congr 2 <;> simp only <;> omega
  have hNE :
      fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogNE R p hp) =
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1 + 2, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 2, by omega⟩ := by
    unfold fkIsingSquareBoundaryRadialPatchFullObservableWindow
      isingLeapfrogNE isingLeapfrogEast isingLeapfrogNorth
    congr 2 <;> simp only <;> omega
  have hC :
      fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p =
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1 + 1, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 1, by omega⟩ := by
    unfold fkIsingSquareBoundaryRadialPatchFullObservableWindow
    congr 2 <;> omega
  rw [hSW, hNW, hSE, hNE, hC]
  exact hphysical


theorem fkIsingSquareBoundaryRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive
    (n m baseI baseJ R rho : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    Complex.normSq
        (fkIsingSquareBoundaryRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p /
            (Real.sqrt (2 * mesh) : Complex) -
          fkIsingSquareBoundaryRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p' /
            (Real.sqrt (2 * mesh) : Complex)) ≤
      (1032080 / (rho : Real) ^ 3) *
        ∑ q, Complex.normSq
          (fkIsingSquareBoundaryRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ q /
            (Real.sqrt (2 * mesh) : Complex)) := by
  let F := fkIsingSquareBoundaryRadialPatchFullObservableWindow
    n m baseI baseJ R hn hm hfitI hfitJ
  have hraw : Complex.normSq (F p - F p') ≤
      (1032080 / (rho : Real) ^ 3) * ∑ q, Complex.normSq (F q) :=
    (fkIsingSquareBoundaryRadialPatchFullObservableWindow_harmonic
      n m baseI baseJ R hn hm hfitI hfitJ).normSq_sub_le_of_diffusiveGradient
        isingLeapfrogDiffusiveGradientBound_fermionic p p' hrho hp hp' hpp'
  have hsqrtSq : Real.sqrt (2 * mesh) ^ 2 = 2 * mesh := by
    rw [Real.sq_sqrt]
    positivity
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by positivity))]
    exact hsqrtSq
  change Complex.normSq
      (F p / (Real.sqrt (2 * mesh) : Complex) -
        F p' / (Real.sqrt (2 * mesh) : Complex)) ≤ _
  rw [← sub_div, hnorm]
  simp_rw [hnorm, ← Finset.sum_div]
  have hden : 0 < 2 * mesh := by positivity
  calc
    Complex.normSq (F p - F p') / (2 * mesh) ≤
        ((1032080 / (rho : Real) ^ 3) *
          ∑ q, Complex.normSq (F q)) / (2 * mesh) :=
      div_le_div_of_nonneg_right hraw hden.le
    _ = _ := by ring


end
end StatMech.Universality
