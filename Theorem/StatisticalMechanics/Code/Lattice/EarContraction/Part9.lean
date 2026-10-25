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
import Def.StatisticalMechanics.Code.Lattice.EarContraction.Part9
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem balanceIsFour_of_contraction (hcontr : BalancePreservingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : BalanceIsFour K a := by
  generalize hn : K.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n IH =>
    subst hn
    rcases Nat.lt_or_ge K.ncard 2 with hlt | hge
    · 
      have h1 : K.ncard = 1 := by
        have hpos : 0 < K.ncard := (Set.ncard_pos hK).mpr hne
        omega
      obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp h1
      subst hv
      exact singleton_balanceIsFour v a
    · 
      obtain ⟨K', hK', hne', a', hlt, hbal⟩ := hcontr K hK hge a
      have hIH := IH K'.ncard hlt K' hK' hne' a' rfl
      unfold BalanceIsFour at hIH ⊢
      rw [← hbal]; exact hIH


theorem simplePolygonCornerBalance_of_contraction (hcontr : BalancePreservingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : SimplePolygonCornerBalance K a :=
  (balanceIsFour_iff_simplePolygon K a).mp (balanceIsFour_of_contraction hcontr K hK hne a)


theorem turningIsFullRevolution_of_contraction (hcontr : BalancePreservingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_simplePolygon K a
    (simplePolygonCornerBalance_of_contraction hcontr K hK hne a)


theorem unitCell_balanceIsFour : BalanceIsFour unitCell ucBase :=
  Or.inr (unitCell_cornerBalance ucBase (Or.inl rfl))


end Lattice
end StatMech
