module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearDeletion.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part4
open scoped BigOperators
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def kwGraphFormalSecondDifference
    {V : Type*} [DecidableEq V]
    (series : MvPowerSeries (Sym2 V) ℂ) (edge : Sym2 V) :
    MvPowerSeries (Sym2 V) ℂ :=
  fun m ↦ ons_secondDifferenceFactor (m edge) *
    MvPowerSeries.coeff m series

end StatMech.FrontierA
