/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusHomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusHomology.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem triangularTorus_surfaceParitySign_eq_spinCharacter
    (a b : Fin 2) (h : Fin 2 × Fin 2) :
    surfaceParitySign
        (surfaceQuadraticParity (triangularTorusSurfaceSpin a b)
          (fun _ => h.1, fun _ => h.2)) =
      ons_spinCharacter a b h := by
  rcases h with ⟨x, y⟩
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [surfaceParitySign, surfaceQuadraticParity,
      triangularTorusSurfaceSpin, ons_spinCharacter, Fin.sum_univ_one,
      Fin.val_add]


theorem triangularTorus_surfaceQuadraticEvenPolynomial_eq
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Complex) (a b : Fin 2) :
    surfaceQuadraticEvenPolynomial (triangularTorusGraph L)
        (triangularTorusSurfaceEdgeClass L)
        (triangularTorusSurfaceSpin a b) weight =
      triangularTorusWeightedSpinCharacterSum L weight a b := by
  classical
  unfold surfaceQuadraticEvenPolynomial
    triangularTorusWeightedSpinCharacterSum evenSubgraphs
  apply Finset.sum_congr rfl
  intro F hF
  rw [triangularTorus_surfaceSubgraphHomology_eq,
    triangularTorus_surfaceParitySign_eq_spinCharacter]

end StatMech.FrontierA
