module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.ClusterBoundaryRecovery.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsEulerParity
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part3
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


noncomputable def boxFrame (m n : ℕ) : Finset (Site 2) :=
  ((Finset.Icc (-1 : ℤ) m).image (fun a => (![a, -1] : Site 2)))
  ∪ ((Finset.Icc (-1 : ℤ) m).image (fun a => (![a, (n:ℤ)] : Site 2)))
  ∪ ((Finset.Icc (-1 : ℤ) n).image (fun b => (![(-1:ℤ), b] : Site 2)))
  ∪ ((Finset.Icc (-1 : ℤ) n).image (fun b => (![(m:ℤ), b] : Site 2)))

end Lattice
end StatMech
