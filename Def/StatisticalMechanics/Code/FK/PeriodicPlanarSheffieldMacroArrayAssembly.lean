/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdjacentHeight.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonSquareEnlarge
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p) (margin : Nat) :
    E.NormalBoundaryBandSeed mu S margin p where
  baseLeft := family.baseLeft
  baseRight := family.baseRight
  baseBottom := family.baseBottom
  baseTop := family.baseTop
  radiusLeft := family.radiusLeft margin
  radiusRight := family.radiusRight margin
  radiusBottom := family.radiusBottom margin
  radiusTop := family.radiusTop margin
  left := family.left margin
  right := family.right margin
  bottom := family.bottom margin
  top := family.top margin


end StatMech.FK.PeriodicPlanar
