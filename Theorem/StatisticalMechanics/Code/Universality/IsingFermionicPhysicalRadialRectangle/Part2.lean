module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part6
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveFiniteIntegration
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareInteriorRadialRectanglePlacement

variable {n : Nat} {hn : 0 < n}

theorem mk_representative
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    Quot.mk _ (representative e) = e :=
  Quotient.out_eq e


end FKIsingSquareInteriorRadialRectanglePlacement
end
end StatMech.Universality
