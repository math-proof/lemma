/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean -/

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
import Def.StatisticalMechanics.Code.Walls.jc_orbitinvariant.Part2
open SimpleGraph Function


namespace StatMech.Walls

open StatMech.Lattice


theorem jc_balancePreservingContractionExtreme_of_rep
    (h : jc_BalancePreservingContractionExtreme) (K : Set (Site 2)) (hK : K.Finite)
    (hge : 2 ≤ K.ncard) (c : Site 2) (hc : IsExtremeCell K c) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧
        cornerBalance K' a' = cornerBalance K (extremeBase K c hc) :=
  h K hK hge c hc


theorem jc_balancePreservingContraction_at_orbit_of_extreme
    (h : jc_BalancePreservingContractionExtreme) (K : Set (Site 2)) (hK : K.Finite)
    (hge : 2 ≤ K.ncard) (c : Site 2) (hc : IsExtremeCell K c)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ)
    (ha : a = (dartNextSub K)^[n] (extremeBase K c hc)) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
  obtain ⟨K', hK', hne', a', hlt, hbal⟩ := h K hK hge c hc
  refine ⟨K', hK', hne', a', hlt, ?_⟩
  rw [hbal, ha, jc_cornerBalance_iterate_dartNextSub K hK (extremeBase K c hc) n]


theorem jc_unitCell_cornerBalance_dartNextSub :
    cornerBalance unitCell (dartNextSub unitCell ucBase) = cornerBalance unitCell ucBase :=
  jc_cornerBalance_dartNextSub unitCell unitCell_finite ucBase


theorem jc_domino_cornerBalance_dartNextSub :
    cornerBalance domino (dartNextSub domino dmBase) = cornerBalance domino dmBase :=
  jc_cornerBalance_dartNextSub domino domino_finite dmBase


end StatMech.Walls
