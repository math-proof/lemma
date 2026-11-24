module
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCut
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus.Part3
public import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
open scoped BigOperators
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

abbrev ons_PlusWiredVertex (d n : Nat) := Option {x // x ∈ box d n}


abbrev ons_PlusWiredBond (d n : Nat) :=
  {edge // edge ∈ bondFinsetTouch d n}


end
end StatMech.Onsager
