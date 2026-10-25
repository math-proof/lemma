/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzEar
open SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def umEar_windowRight (K : Set (Site 2)) (e : Dart) (a b : ℕ) : ℤ := by
  classical
  exact (((Finset.Ico a b).filter (fun i => turnZ K ((dartNext K)^[i] e) = 1)).card : ℤ)


noncomputable def umEar_windowLeft (K : Set (Site 2)) (e : Dart) (a b : ℕ) : ℤ := by
  classical
  exact (((Finset.Ico a b).filter (fun i => turnZ K ((dartNext K)^[i] e) = -1)).card : ℤ)


end Lattice
end StatMech
