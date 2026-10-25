/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardFlatSpinor
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitUnitCycleReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainHomology
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplitCycleReversal
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardShiftedCycleAssembly
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u

noncomputable def surfaceSpinFormalEvenPolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) :
    MvPowerSeries (Sym2 V) Complex :=
  ∑ F ∈ evenSubgraphs G,
    MvPowerSeries.monomial (ons_finsetExponent F)
      (surfaceSpinCycleCoefficient edgeClass lambda F)

noncomputable def surfaceSpinEvenMvPolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) :
    MvPolynomial (Sym2 V) Complex :=
  ∑ F ∈ evenSubgraphs G,
    MvPolynomial.monomial (ons_finsetExponent F)
      (surfaceSpinCycleCoefficient edgeClass lambda F)

end StatMech.FrontierA
