module
public import Theorem.StatisticalMechanics.Code.SLE.BrownianProjectiveContent
public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.MetricSpace.Bounded
public import Theorem.StatisticalMechanics.Code.SLE.BrownianCompactCylinderIntersection
open MeasureTheory Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianCompactCylinderIntersection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.SLE

noncomputable def cylinderPrefixSupport
    (I : Nat -> Finset Real) (n : Nat) : Finset Real :=
  (Finset.range (n + 1)).biUnion I

end StatMech.SLE
