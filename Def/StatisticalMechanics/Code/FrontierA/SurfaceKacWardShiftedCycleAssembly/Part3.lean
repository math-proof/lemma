module
public import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardFlatSpinor
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitUnitCycleReduction
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainHomology
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplitCycleReversal
public import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardShiftedCycleAssembly.Part2
open scoped BigOperators
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u

noncomputable def surfaceSpinScalePolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (weight : Sym2 V -> Complex) : Polynomial Complex :=
  ∑ F ∈ evenSubgraphs G,
    Polynomial.monomial F.card
      (surfaceSpinCycleCoefficient edgeClass lambda F *
        ∏ edge ∈ F, weight edge)

end StatMech.FrontierA
