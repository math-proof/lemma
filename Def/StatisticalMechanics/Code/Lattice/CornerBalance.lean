/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean -/

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
open SimpleGraph Function


namespace StatMech

namespace Lattice

open Classical in


noncomputable def rightCornerCount (K : Set (Site 2)) (e : Dart) (p : ℕ) : ℤ :=
  ((Finset.range p).filter (fun i => turnZ K ((dartNext K)^[i] e) = 1)).card

open Classical in


noncomputable def leftCornerCount (K : Set (Site 2)) (e : Dart) (p : ℕ) : ℤ :=
  ((Finset.range p).filter (fun i => turnZ K ((dartNext K)^[i] e) = -1)).card


end Lattice
end StatMech
