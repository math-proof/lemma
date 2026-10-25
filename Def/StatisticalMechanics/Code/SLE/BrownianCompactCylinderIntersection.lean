/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianCompactCylinderIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianProjectiveContent
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.MetricSpace.Bounded
import Theorem.StatisticalMechanics.Code.SLE.BrownianCompactCylinderIntersection
open MeasureTheory Set


namespace StatMech.SLE

noncomputable def cylinderPrefixSupport
    (I : Nat -> Finset Real) (n : Nat) : Finset Real :=
  (Finset.range (n + 1)).biUnion I

end StatMech.SLE
