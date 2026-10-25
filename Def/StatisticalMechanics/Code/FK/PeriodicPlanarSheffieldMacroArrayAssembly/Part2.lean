/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdjacentHeight.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonSquareEnlarge
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.horizontalRadiusRequirement
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (horizontalMargin : Nat) : Nat :=
  max
    (((family.radiusLeft horizontalMargin : Int) +
      family.baseLeft 1 - family.baseBottom 1).toNat)
    (((family.radiusRight horizontalMargin : Int) +
      family.baseRight 1 - family.baseBottom 1).toNat)


def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.verticalRadiusRequirement
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalMargin : Nat) : Nat :=
  max
    (((family.radiusBottom verticalMargin : Int) +
      family.baseBottom 0 - family.baseLeft 0).toNat)
    (((family.radiusTop verticalMargin : Int) +
      family.baseTop 0 - family.baseLeft 0).toNat)

end StatMech.FK.PeriodicPlanar
