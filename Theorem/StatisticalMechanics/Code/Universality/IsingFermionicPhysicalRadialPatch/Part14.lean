/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part14


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareGrowingRadialPrimalPrimitive_apply
    (m : Nat → Nat) (hm : ∀ n, m n ≤ n) (base : Nat → Real)
    (n : Nat) (hmn : 0 < m n)
    (p : FKIsingSquareRadialPatchPrimalNode (m n)) :
    fkIsingSquareGrowingRadialPrimalPrimitive m hm base n
        (fkIsingSquareRadialPatchPrimalNodeVertex n (m n) (hm n) p) =
      base n + fkIsingSquareRadialPatchPrimitive
        n (m n) (lt_of_lt_of_le hmn (hm n)) (hm n) hmn
          p.1.1.1 p.1.2.1 := by
  simp only [fkIsingSquareGrowingRadialPrimalPrimitive, dif_pos hmn]
  exact fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply _ _ _ _ _ _ _


theorem fkIsingSquareRadialPatchPrimitive_uniform_convergence_to_imPhi
    (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
    (Phi : Complex → Complex)
    (upper lower harmonic physical :
      ∀ n, (fkSquareBoxPlanar n).V → Real)
    (eps : Nat → Real) (m : Nat → Nat) (base : Nat → Real)
    (hm : ∀ n, m n ≤ n)
    (hmpos : ∀ᶠ n in atTop, 0 < m n)
    (hupper : ∀ n, IsingFiniteGraphSubharmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (upper n))
    (hlower : ∀ n, IsingFiniteGraphSuperharmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (lower n))
    (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
    (hupperBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      upper n x ≤ harmonic n x + eps n)
    (hlowerBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      harmonic n x ≤ lower n x + eps n)
    (hsandwich : ∀ n x,
      lower n x ≤ physical n x ∧ physical n x ≤ upper n x)
    (heps : Tendsto eps atTop (nhds 0))
    (hdirichlet : ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x,
        |harmonic n x - fkIsingSquareSampledImaginaryPart
          embedding Phi n x| < eta)
    (hidentify : ∀ n (hn : 0 < n) (hmn : 0 < m n)
      (i j : Fin (m n)), Even (i.1 + j.1) →
      base n + fkIsingSquareRadialPatchPrimitive
          n (m n) hn (hm n) hmn i.1 j.1 =
        physical n (fkIsingSquareRadialPatchVertex n (m n) (hm n) i j)) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ (hmn : 0 < m n)
        (i j : Fin (m n)), Even (i.1 + j.1) →
        |base n + fkIsingSquareRadialPatchPrimitive
              n (m n) (lt_of_lt_of_le hmn (hm n)) (hm n) hmn i.1 j.1 -
            fkIsingSquareSampledImaginaryPart embedding Phi n
              (fkIsingSquareRadialPatchVertex n (m n) (hm n) i j)| < eta := by
  intro eta heta
  have hfull := fkIsingSquare_physicalPrimitive_uniform_convergence_to_imPhi
    embedding Phi upper lower harmonic physical eps hupper hlower hharmonic
    hupperBoundary hlowerBoundary hsandwich heps hdirichlet eta heta
  filter_upwards [hfull, hmpos] with n hnconv hmn
  intro hmn' i j heven
  have hn : 0 < n := lt_of_lt_of_le hmn (hm n)
  rw [hidentify n hn hmn' i j heven]
  exact hnconv (fkIsingSquareRadialPatchVertex n (m n) (hm n) i j)


theorem fkIsingSquareGrowingRadialPrimalPrimitive_uniform_convergence_to_imPhi
    (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
    (Phi : Complex → Complex)
    (upper lower harmonic : ∀ n, (fkSquareBoxPlanar n).V → Real)
    (eps : Nat → Real) (m : Nat → Nat) (base : Nat → Real)
    (hm : ∀ n, m n ≤ n)
    (hmpos : ∀ᶠ n in atTop, 0 < m n)
    (hupper : ∀ n, IsingFiniteGraphSubharmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (upper n))
    (hlower : ∀ n, IsingFiniteGraphSuperharmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (lower n))
    (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
    (hupperBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      upper n x ≤ harmonic n x + eps n)
    (hlowerBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      harmonic n x ≤ lower n x + eps n)
    (hsandwich : ∀ n x,
      lower n x ≤ fkIsingSquareGrowingRadialPrimalPrimitive m hm base n x ∧
        fkIsingSquareGrowingRadialPrimalPrimitive m hm base n x ≤ upper n x)
    (heps : Tendsto eps atTop (nhds 0))
    (hdirichlet : ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x,
        |harmonic n x - fkIsingSquareSampledImaginaryPart
          embedding Phi n x| < eta) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ (p : FKIsingSquareRadialPatchPrimalNode (m n)),
        |base n + fkIsingSquareRadialPatchPrimitive
              n (m n)
              (lt_of_lt_of_le (Nat.zero_lt_of_lt p.1.1.2) (hm n))
              (hm n) (Nat.zero_lt_of_lt p.1.1.2) p.1.1.1 p.1.2.1 -
            fkIsingSquareSampledImaginaryPart embedding Phi n
              (fkIsingSquareRadialPatchPrimalNodeVertex n (m n) (hm n) p)| < eta := by
  intro eta heta
  have hfull := fkIsingSquare_physicalPrimitive_uniform_convergence_to_imPhi
    embedding Phi upper lower harmonic
    (fkIsingSquareGrowingRadialPrimalPrimitive m hm base) eps
    hupper hlower hharmonic hupperBoundary hlowerBoundary hsandwich
    heps hdirichlet eta heta
  filter_upwards [hfull, hmpos] with n hnconv hmn
  intro p
  rw [← fkIsingSquareGrowingRadialPrimalPrimitive_apply m hm base n hmn p]
  exact hnconv (fkIsingSquareRadialPatchPrimalNodeVertex n (m n) (hm n) p)


end
end StatMech.Universality
