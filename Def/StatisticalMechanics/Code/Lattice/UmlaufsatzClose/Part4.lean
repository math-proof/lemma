module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzBaseCases.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzEar.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnetEar
public import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzClose.Part3
open SimpleGraph Function Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

noncomputable def uc_rotSub (K : Set (Site 2)) :
    {e : Dart // IsBoundaryDart K e} → {e : Dart // IsBoundaryDart (uc_rotSet K) e} :=
  fun a => ⟨uc_rotDart a.1, uc_rotDart_boundary K a.1 a.2⟩

end Lattice
end StatMech
