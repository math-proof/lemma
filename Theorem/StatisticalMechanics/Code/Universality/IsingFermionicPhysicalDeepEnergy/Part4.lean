/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactVariation.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactEnergy
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDeepEnergy.Part3


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatchWindowCell_injective
    (m baseI baseJ R : Nat)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    Function.Injective
      (fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ) := by
  intro p q hpq
  have hx := congrArg (fun c : FKIsingSquareRadialPatchInteriorCell m ↦ c.1.1) hpq
  have hy := congrArg (fun c : FKIsingSquareRadialPatchInteriorCell m ↦ c.2.1) hpq
  change baseI + p.1.1 = baseI + q.1.1 at hx
  change baseJ + p.2.1 = baseJ + q.2.1 at hy
  apply Prod.ext <;> apply Fin.ext <;> omega


theorem fkIsingSquareRadialPatchFullObservableWindow_deep_energy_le
    (n m baseI baseJ R : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat) (base : Real)
    (hdeep : ∀ p : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
    mesh ^ 2 *
        ∑ p : IsingLeapfrogBox R,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservableWindow
                n m baseI baseJ R hn hm hfitI hfitJ p /
              (Real.sqrt (2 * mesh) : Complex)) ≤
      mesh *
        ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
          |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) +
        ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
          |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) := by
  classical
  let cell := fkIsingSquareRadialPatchWindowCell
    m baseI baseJ R hfitI hfitJ
  let C := fkIsingSquareRadialPatchDeepCells n m hm hm2 r
  let energy := fun c : FKIsingSquareRadialPatchInteriorCell m ↦
    Complex.normSq
      (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
        (Real.sqrt (2 * mesh) : Complex))
  have himage : Finset.univ.image cell ⊆ C := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    exact hdeep p
  have hsum : (∑ p : IsingLeapfrogBox R, energy (cell p)) ≤
      ∑ c ∈ C, energy c := by
    rw [← Finset.sum_image
      (fkIsingSquareRadialPatchWindowCell_injective
        m baseI baseJ R hfitI hfitJ).injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg himage
      (fun c _ _ ↦ Complex.normSq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hsum (sq_nonneg mesh)
  have hdeepEnergy :=
    fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_le
      n m mesh hn hm hm2 hmesh r base
  calc
    _ = mesh ^ 2 * ∑ p : IsingLeapfrogBox R, energy (cell p) := by
      congr 1
    _ ≤ mesh ^ 2 * ∑ c ∈ C, energy c := hscaled
    _ ≤ _ := hdeepEnergy


theorem fkIsingSquareRadialPatchFullObservableWindow_deep_diffusive
    (n m baseI baseJ R rho : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat) (base : Real)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    mesh ^ 2 * Complex.normSq
        (fkIsingSquareRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p /
            (Real.sqrt (2 * mesh) : Complex) -
          fkIsingSquareRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p' /
            (Real.sqrt (2 * mesh) : Complex)) ≤
      (1032080 / (rho : Real) ^ 3) * mesh *
        ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
          |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) +
        ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
          |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) := by
  have hgradient :=
    fkIsingSquareRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive
      n m baseI baseJ R rho mesh hn hm hfitI hfitJ hmesh
      p p' hrho hp hp' hpp'
  have henergy :=
    fkIsingSquareRadialPatchFullObservableWindow_deep_energy_le
      n m baseI baseJ R mesh hn hm hm2 hfitI hfitJ hmesh r base hdeep
  have hfactor : 0 ≤ 1032080 / (rho : Real) ^ 3 := by positivity
  calc
    _ ≤ mesh ^ 2 *
        ((1032080 / (rho : Real) ^ 3) *
          ∑ q : IsingLeapfrogBox R,
            Complex.normSq
              (fkIsingSquareRadialPatchFullObservableWindow
                  n m baseI baseJ R hn hm hfitI hfitJ q /
                (Real.sqrt (2 * mesh) : Complex))) :=
      mul_le_mul_of_nonneg_left hgradient (sq_nonneg mesh)
    _ = (1032080 / (rho : Real) ^ 3) *
        (mesh ^ 2 *
          ∑ q : IsingLeapfrogBox R,
            Complex.normSq
              (fkIsingSquareRadialPatchFullObservableWindow
                  n m baseI baseJ R hn hm hfitI hfitJ q /
                (Real.sqrt (2 * mesh) : Complex))) := by ring
    _ ≤ (1032080 / (rho : Real) ^ 3) *
        (mesh *
          ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts
              n m hm (by omega) r,
            |fkIsingSquareRadialPatchPrimalValue
                n m hn hm (by omega) base d.snd -
              fkIsingSquareRadialPatchPrimalValue
                n m hn hm (by omega) base d.fst|) +
          ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
            |fkIsingSquareRadialPatchDualValue
                n m hn hm (by omega) base d.snd -
              fkIsingSquareRadialPatchDualValue
                n m hn hm (by omega) base d.fst|)) :=
      mul_le_mul_of_nonneg_left henergy hfactor
    _ = _ := by ring

end
end StatMech.Universality
