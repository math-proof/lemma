module
public import Theorem.StatisticalMechanics.Code.SLE.BrownianProjectiveContent
public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.MetricSpace.Bounded
public import Theorem.StatisticalMechanics.Code.SLE.BrownianCompactCylinderIntersection.Part2
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

noncomputable def cylinderPrefixBase
    (I : Nat -> Finset Real) (L : forall k, Set (I k -> Real))
    (n : Nat) : Set (cylinderPrefixSupport I n -> Real) :=
  {x | forall (k : Nat) (hkn : k <= n),
    Finset.restrict₂
      (π := fun _ : Real => Real)
      (cylinderPrefixSupport_subset I hkn) x ∈ L k}


end StatMech.SLE
