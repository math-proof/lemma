/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.BalanceContraction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnetEar
import Def.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem bpc_notProbed_of_not_footprint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2)
    (hc : c ∉ bpc_orbitFootprint K a) (i : ℕ) :
    bpc_NotProbed c ((dartNext K)^[i] a.1) := by
  constructor
  · intro h; exact hc ⟨i, Or.inl h.symm⟩
  · intro h; exact hc ⟨i, Or.inr (Or.inl h.symm)⟩


theorem bpc_ne_tail_of_not_footprint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2)
    (hc : c ∉ bpc_orbitFootprint K a) : c ≠ a.1.tail := by
  intro h
  apply hc
  exact ⟨0, Or.inr (Or.inr (by rw [Function.iterate_zero_apply]; exact h))⟩


theorem bpc_contraction_of_not_saturating (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) (hcK : c ∈ K)
    (hc : c ∉ bpc_orbitFootprint K a) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
  have hne_tail : c ≠ a.1.tail := bpc_ne_tail_of_not_footprint K a c hc
  have hbd : IsBoundaryDart (K \ {c}) a.1 :=
    bpc_isBoundaryDart_diff_singleton K c a.1 a.2 hne_tail
  refine ⟨K \ {c}, hK.subset Set.diff_subset, ⟨a.1.tail, hbd.1⟩, ⟨a.1, hbd⟩, ?_, ?_⟩
  · have hsub : (K \ {c}) ⊂ K := by
      rw [Set.ssubset_iff_of_subset Set.diff_subset]
      exact ⟨c, hcK, by simp⟩
    exact Set.ncard_lt_ncard hsub hK
  · exact bpc_cornerBalance_diff_singleton K c a ⟨a.1, hbd⟩ rfl
      (bpc_notProbed_of_not_footprint K a c hc)


end Lattice
end StatMech
