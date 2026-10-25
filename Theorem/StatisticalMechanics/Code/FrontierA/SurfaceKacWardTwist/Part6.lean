/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part6
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

theorem surfaceTwistedKacWardMatrix_apply {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (edgeClass : Sym2 V → SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Complex)
    (d e : G.Dart) :
    surfaceTwistedKacWardMatrix G phase edgeClass lambda weight d e =
      if d.snd = e.fst ∧ d.edge ≠ e.edge then
        surfaceHomologyCharacter lambda (edgeClass d.edge) *
          weight d.edge * phase d e
      else 0 := by
  simp [surfaceTwistedKacWardMatrix, kwGraphTransition,
    surfaceTwistedEdgeWeight, mul_assoc]


theorem surface_twisted_kacWard_det_square_of_base {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (edgeClass : Sym2 V → SurfaceHomology g)
    (hbase : ∀ w : Sym2 V → Complex,
      (1 - kwGraphTransition G w phase).det =
        surfaceQuadraticEvenPolynomial G edgeClass
          (0 : SurfaceSpinStructure g) w ^ 2)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Complex) :
    (1 - surfaceTwistedKacWardMatrix G phase edgeClass lambda weight).det =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
  unfold surfaceTwistedKacWardMatrix
  rw [hbase, surfaceQuadraticEvenPolynomial_twist]


end
end StatMech.FrontierA
