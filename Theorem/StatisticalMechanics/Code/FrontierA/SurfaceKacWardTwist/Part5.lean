/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part5
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

theorem surfaceParitySign_quadratic_twist {g : Nat}
    (lambda : SurfaceSpinStructure g) (h : SurfaceHomology g) :
    (surfaceParitySign (surfaceQuadraticParity lambda h) : Complex) =
      (surfaceParitySign (surfaceBaseQuadraticParity h) : Complex) *
        surfaceHomologyCharacter lambda h := by
  rw [surfaceQuadraticParity_eq_base_add_linear, surfaceParitySign_add]
  unfold surfaceHomologyCharacter
  push_cast
  rfl

theorem surfaceQuadraticEvenPolynomial_twist {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Complex) :
    surfaceQuadraticEvenPolynomial G edgeClass
        (0 : SurfaceSpinStructure g)
        (surfaceTwistedEdgeWeight edgeClass lambda weight) =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight := by
  unfold surfaceQuadraticEvenPolynomial
  apply Finset.sum_congr rfl
  intro F hF
  rw [prod_surfaceTwistedEdgeWeight, surfaceQuadraticParity_zero,
    surfaceParitySign_quadratic_twist]
  ring

end
end StatMech.FrontierA
