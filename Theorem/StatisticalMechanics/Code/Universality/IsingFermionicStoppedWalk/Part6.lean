/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part7


namespace StatMech.Universality

open Finset

noncomputable section

theorem fkIsingSquareRadialPatchFullObservableWindow_harmonic
    (n m baseI baseJ R : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    IsingLeapfrogHarmonicOnBox R
      (fkIsingSquareRadialPatchFullObservableWindow
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
    fkIsingSquareRadialPatchFullObservable_leapfrog_harmonic
      n m (baseI + p.1.1 - 1) (baseJ + p.2.1 - 1) hn hm
      (by omega) (by omega)
  have hSW :
      fkIsingSquareRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogSW R p) =
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1, by omega⟩
          ⟨baseJ + p.2.1 - 1, by omega⟩ := by
    unfold fkIsingSquareRadialPatchFullObservableWindow
      isingLeapfrogSW isingLeapfrogWest isingLeapfrogSouth
    congr 2 <;> simp only <;> omega
  have hNW :
      fkIsingSquareRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogNW R p hp) =
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 2, by omega⟩ := by
    unfold fkIsingSquareRadialPatchFullObservableWindow
      isingLeapfrogNW isingLeapfrogWest isingLeapfrogNorth
    congr 2 <;> simp only <;> omega
  have hSE :
      fkIsingSquareRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogSE R p hp) =
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1 + 2, by omega⟩
          ⟨baseJ + p.2.1 - 1, by omega⟩ := by
    unfold fkIsingSquareRadialPatchFullObservableWindow
      isingLeapfrogSE isingLeapfrogEast isingLeapfrogSouth
    congr 2 <;> simp only <;> omega
  have hNE :
      fkIsingSquareRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogNE R p hp) =
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1 + 2, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 2, by omega⟩ := by
    unfold fkIsingSquareRadialPatchFullObservableWindow
      isingLeapfrogNE isingLeapfrogEast isingLeapfrogNorth
    congr 2 <;> simp only <;> omega
  have hC :
      fkIsingSquareRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p =
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1 + 1, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 1, by omega⟩ := by
    unfold fkIsingSquareRadialPatchFullObservableWindow
    congr 2 <;> omega
  rw [hSW, hNW, hSE, hNE, hC]
  exact hphysical


theorem fkIsingSquareRadialPatchFullObservableWindow_normSq_sub_le
    (n m baseI baseJ R : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (t : Nat) (p p' : IsingLeapfrogBox R) :
    Complex.normSq
        (fkIsingSquareRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ p -
          fkIsingSquareRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ p') ≤
      isingLeapfrogStoppedKernelGradientSq R t p p' *
        ∑ q, Complex.normSq
          (fkIsingSquareRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ q) := by
  exact (fkIsingSquareRadialPatchFullObservableWindow_harmonic
    n m baseI baseJ R hn hm hfitI hfitJ).normSq_sub_le_kernelGradient t p p'

end
end StatMech.Universality
