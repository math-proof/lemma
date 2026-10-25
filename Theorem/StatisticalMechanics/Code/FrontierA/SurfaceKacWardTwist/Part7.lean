/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

theorem surfaceTwistedSectorRoot_graphSectorWeight {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology g)
    (weight : Sym2 V → Real) (lambda : SurfaceSpinStructure g) :
    surfaceTwistedSectorRoot
        (surfaceGraphSectorWeight G edgeClass weight) lambda =
      ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
        surfaceParitySign
          (surfaceQuadraticParity lambda
            (surfaceSubgraphHomology edgeClass F)) *
          ∏ edge ∈ F, weight edge := by
  unfold surfaceTwistedSectorRoot surfaceGraphSectorWeight
  calc
    (∑ h : SurfaceHomology g,
        surfaceParitySign (surfaceQuadraticParity lambda h) *
          ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph with
              surfaceSubgraphHomology edgeClass F = h,
            ∏ edge ∈ F, weight edge) =
      ∑ h : SurfaceHomology g,
        ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph with
            surfaceSubgraphHomology edgeClass F = h,
          surfaceParitySign
              (surfaceQuadraticParity lambda
                (surfaceSubgraphHomology edgeClass F)) *
            ∏ edge ∈ F, weight edge := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F hF
      rw [(Finset.mem_filter.mp hF).2]
    _ = _ := Finset.sum_fiberwise
      (G.edgeFinset.powerset.filter IsEvenSubgraph)
      (surfaceSubgraphHomology edgeClass)
      (fun F => surfaceParitySign
        (surfaceQuadraticParity lambda
          (surfaceSubgraphHomology edgeClass F)) *
        ∏ edge ∈ F, weight edge)

theorem surfaceQuadraticEvenPolynomial_real_eq_sectorRoot {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology g)
    (weight : Sym2 V → Real) (lambda : SurfaceSpinStructure g) :
    surfaceQuadraticEvenPolynomial G edgeClass lambda
        (fun edge => (weight edge : Complex)) =
      (surfaceTwistedSectorRoot
        (surfaceGraphSectorWeight G edgeClass weight) lambda : Complex) := by
  rw [surfaceTwistedSectorRoot_graphSectorWeight]
  unfold surfaceQuadraticEvenPolynomial
  push_cast
  rfl


theorem surface_twisted_kacWard_det_eq_sectorSquare_of_base {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (edgeClass : Sym2 V → SurfaceHomology g)
    (hbase : ∀ w : Sym2 V → Complex,
      (1 - kwGraphTransition G w phase).det =
        surfaceQuadraticEvenPolynomial G edgeClass
          (0 : SurfaceSpinStructure g) w ^ 2)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Real) :
    (1 - surfaceTwistedKacWardMatrix G phase edgeClass lambda
        (fun edge => (weight edge : Complex))).det =
      (surfaceTwistedSectorSquare
        (surfaceGraphSectorWeight G edgeClass weight) lambda : Complex) := by
  rw [surface_twisted_kacWard_det_square_of_base G phase edgeClass hbase,
    surfaceQuadraticEvenPolynomial_real_eq_sectorRoot]
  simp [surfaceTwistedSectorSquare]

end
end StatMech.FrontierA
