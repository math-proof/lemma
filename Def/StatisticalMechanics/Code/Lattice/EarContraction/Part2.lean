/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction
open SimpleGraph Function


namespace StatMech

namespace Lattice

def CellConnected (K : Set (Site 2)) : Prop :=
  ((hypercubicLattice 2).induce K).Connected


noncomputable def diffEquiv (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K) :
    {x : K // x ≠ (⟨c, hc⟩ : K)} ≃ ↑(K \ {c}) where
  toFun := fun x => ⟨x.1.1, by
    refine ⟨x.1.2, ?_⟩
    simp only [Set.mem_singleton_iff]; intro h; exact x.2 (Subtype.ext h)⟩
  invFun := fun y => ⟨⟨y.1, y.2.1⟩, by
    intro h; exact y.2.2 (Set.mem_singleton_iff.mpr (congrArg Subtype.val h))⟩
  left_inv := fun _ => by rfl
  right_inv := fun _ => by rfl


noncomputable def diffIso (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K) :
    (((hypercubicLattice 2).induce K).induce {(⟨c, hc⟩ : K)}ᶜ) ≃g
      ((hypercubicLattice 2).induce (K \ {c})) where
  toEquiv := diffEquiv K c hc
  map_rel_iff' := by intro a b; rfl


end Lattice
end StatMech
