module
public import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
public import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
public import Abbrev.StatisticalMechanics.Code.Sharpness.CToOneLattice
open Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

open Ising Lattice


noncomputable instance sctBoxFintype (d n : ℕ) : Fintype (sctBox d n) :=
  (box_finite d n).fintype


end Sharpness
end StatMech
