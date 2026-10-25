/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceReduction
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly.Part2
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u


noncomputable def surfaceBaseFormalEvenPolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g) :
    MvPowerSeries (Sym2 V) Complex :=
  ∑ F ∈ evenSubgraphs G,
    MvPowerSeries.monomial (ons_finsetExponent F)
      (surfaceBaseCycleCoefficient edgeClass F)


noncomputable def surfaceBaseEvenMvPolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g) :
    MvPolynomial (Sym2 V) Complex :=
  ∑ F ∈ evenSubgraphs G,
    MvPolynomial.monomial (ons_finsetExponent F)
      (surfaceBaseCycleCoefficient edgeClass F)

end StatMech.FrontierA
