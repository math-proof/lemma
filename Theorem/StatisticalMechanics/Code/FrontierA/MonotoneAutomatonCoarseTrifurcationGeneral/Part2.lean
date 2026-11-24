module
public import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseProbabilityGeneral.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonFiniteMerge.Part2
public import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof.Part3
public import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonCoarseTrifurcationGeneral
open MeasureTheory Set
open scoped ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}


theorem measurableSet_siteBgfdFaithfulAllOpenTrifAt (d n : ℕ) :
    MeasurableSet (SiteBgfdFaithfulAllOpenTrifAt d n) :=
  measurable_siteToBond (measurableSet_bgfdFaithfulAllOpenTrifAt n 0)


end StatMech.FrontierA
