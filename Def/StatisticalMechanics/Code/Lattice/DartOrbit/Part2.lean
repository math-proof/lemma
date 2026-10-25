/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part2
open SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def dartSuccGraph (K : Set (Site 2)) :
    SimpleGraph {e : Dart // IsBoundaryDart K e} where
  Adj a b := a ≠ b ∧ (dartNextSub K a = b ∨ dartNextSub K b = a)
  symm := by constructor; rintro a b ⟨hne, h⟩; exact ⟨hne.symm, h.symm⟩
  loopless := by refine ⟨?_⟩; rintro a ⟨hne, _⟩; exact hne rfl


end Lattice
end StatMech
