module
public import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part5
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
open Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationClosure.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open BeffaraDC FrontierA


def TriHexSurfacePercolationEquivalence (q p : Real) : Prop :=
  triangular.wiredPercolates p q <->
    hexagonal.wiredPercolates (dualParam p q) q


end StatMech.FK.PeriodicPlanar
