module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
public import Def.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part3
open SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

theorem interfaceConnected_of_orbitHeadsSaturate (K : Set (Site 2))
    (h : OrbitHeadsSaturate K) : InterfaceConnected K := by
  intro e f he hf hreach
  exact h e f he hf (fun _he' _hf' => hreach)


theorem orbitHeadsSaturate_of_interfaceConnected (K : Set (Site 2))
    (h : InterfaceConnected K) : OrbitHeadsSaturate K := by
  intro e f he hf hreach
  exact h e f he hf (hreach he hf)


end Lattice
end StatMech
