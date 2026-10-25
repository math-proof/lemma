/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


theorem hexFiniteRegion_single_length (a w : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hsaw : (ofTurns a h0 ts).IsSAW)
    (hstay : (ofTurns a h0 ts).StaysIn (hexFiniteRegion_single a w hclosure).inRegion) :
    ts = [] := by
  have hlt := (hexFiniteRegion_single a w hclosure).length_lt a h0 ts hsaw hstay
  simp only [hexFiniteRegion_single, Finset.card_singleton] at hlt
  exact List.eq_nil_of_length_eq_zero (by omega)

end StatMech.Universality
