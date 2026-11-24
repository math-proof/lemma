module
public import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part5
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
public import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part4
open scoped BigOperators
open Finset SimpleGraph
set_option linter.unusedDecidableInType false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

theorem prod_surfaceTwistedEdgeWeight {g : Nat} {V : Type*}
    [DecidableEq V] (edgeClass : Sym2 V → SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Complex)
    (F : Finset (Sym2 V)) :
    (∏ edge ∈ F, surfaceTwistedEdgeWeight edgeClass lambda weight edge) =
      surfaceHomologyCharacter lambda (surfaceSubgraphHomology edgeClass F) *
        ∏ edge ∈ F, weight edge := by
  unfold surfaceTwistedEdgeWeight surfaceSubgraphHomology
  rw [Finset.prod_mul_distrib,
    surfaceHomologyCharacter_finset_sum]

end
end StatMech.FrontierA
