/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectedMatchingCut
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.GhostCurrentRep

noncomputable section

variable {W : Type*} [DecidableEq W]


theorem lpFiveToggle14_orbitGH
    (Si Sj T : Finset W) :
    lpFiveToggle14 T (lpFiveOrbitGHNeg Si Sj T) =
      lpFiveOrbitGHPos Si Sj T := by
  apply LPFiveSourceAllocation.ext <;>
    simp only [lpFiveToggle14, lpFiveOrbitGHNeg, lpFiveOrbitGHPos]
  all_goals
    ext x
    simp only [Finset.mem_symmDiff, Finset.notMem_empty]
    tauto


theorem lpMatchingFiveCurrentCoefficient_eq_disconnectionResidues
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1)
    (i j : I) :
    let Si := lpMatchingSeamSource left right i
    let Sj := lpMatchingSeamSource left right j
    let T := lpMatchingGhostSource g0 g1
    let Z := currentSum G beta J ∅
    let C := currentSum G beta J T
    lpMatchingFiveCurrentCoefficient G beta J left right g0 g1 i j =
      sourcePairDisconnSum G beta J (Si ∆ Sj ∆ T) ∅ g0 g1 *
          Z * (Z ^ 2 - C ^ 2) -
        2 * currentSum G beta J Si *
          sourcePairDisconnSum G beta J (Sj ∆ T) ∅ g0 g1 * Z ^ 2 +
        2 * sourcePairDisconnSum G beta J (Si ∆ T) ∅ g0 g1 *
          currentSum G beta J (Sj ∆ T) * C * Z := by
  dsimp only
  let Si := lpMatchingSeamSource left right i
  let Sj := lpMatchingSeamSource left right j
  let T := lpMatchingGhostSource g0 g1
  let Z := currentSum G beta J ∅
  let C := currentSum G beta J T
  have hT : T = ({g0, g1} : Finset W) := by
    ext x
    simp only [T, lpMatchingGhostSource, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hg⟩
      · exact Or.inr ⟨rfl, hg.symm⟩
  have hR := gcr_currentSum_ghostRep G beta J (Si ∆ Sj ∆ T) hg
  have hJ := gcr_currentSum_ghostRep G beta J (Sj ∆ T) hg
  have hI := gcr_currentSum_ghostRep G beta J (Si ∆ T) hg
  rw [← hT, symmDiff_symmDiff_cancel_right] at hR hJ hI
  unfold lpMatchingFiveCurrentCoefficient lpFiveCurrentSourceMass
  dsimp only [Si, Sj, T, Z, C] at hR hJ hI ⊢
  calc
    _ = (currentSum G beta J (Si ∆ Sj ∆ T) * Z -
            currentSum G beta J (Si ∆ Sj) * C) * Z ^ 3 -
          (currentSum G beta J (Si ∆ Sj ∆ T) * Z -
            currentSum G beta J (Si ∆ Sj) * C) * C ^ 2 * Z -
          2 * currentSum G beta J Si *
            (currentSum G beta J (Sj ∆ T) * Z -
              currentSum G beta J Sj * C) * Z ^ 2 +
          2 * (currentSum G beta J (Si ∆ T) * Z -
              currentSum G beta J Si * C) *
            currentSum G beta J (Sj ∆ T) * C * Z := by ring
    _ = _ := by rw [hR, hJ, hI]; ring


end
end StatMech.Ising
