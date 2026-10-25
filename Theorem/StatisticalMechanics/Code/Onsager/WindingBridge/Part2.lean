/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.InteriorReaches
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Def.StatisticalMechanics.Code.Onsager.WindingBridge.Part2


namespace StatMech.Onsager.WindingBridge

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches


theorem preS_finite (S : Set (Site 2)) (hfin : S.Finite) : (preS S).Finite :=
  Set.Finite.preimage (toSite_injective.injOn) hfin


theorem shiftPre_finite (S : Set (Site 2)) (hfin : S.Finite) :
    {p : Pt | toSite (p.1 + 1, p.2) ∈ S}.Finite :=
  Set.Finite.preimage ((toSite_injective.comp shift_injective).injOn) hfin


end StatMech.Onsager.WindingBridge
