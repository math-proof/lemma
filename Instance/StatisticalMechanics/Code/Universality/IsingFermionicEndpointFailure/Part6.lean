/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part18


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingOrderedFarHorizontalEndpointFamily_finite
    (m R t : Nat) (mark target : IsingLineBox R)
    (startY targetY : Int) :
    Finite (IsingOrderedFarHorizontalEndpointFamily
      m R t mark target startY targetY) := by
  letI (k : Fin (t + 1)) : Fintype (Fin k) := inferInstance
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (IsingLineFirstEndpointFamily R (k - j) mark target) :=
    Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype (VerticalChoicePathFamily k startY targetY) := Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - k} :=
    (List.finite_length_eq (Bool × Bool) (t - k)).fintype
  unfold IsingOrderedFarHorizontalEndpointFamily
  infer_instance

end
end StatMech.Universality
