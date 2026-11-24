module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
public import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing
open Set SimpleGraph Topology
open scoped unitInterval


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


noncomputable def gridConnector (x y : Site 2) :
    (hypercubicLattice 2).Walk x y :=
  (sw_lshape (x 0) (x 1) (y 0) (y 1)).copy
    (site_eq_vec x).symm (site_eq_vec y).symm

end ContinuousRectangleCrossing
end StatMech
