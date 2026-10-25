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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part17


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingOrderedFarEndpointFamily_finite
    (m n t : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) :
    Finite (IsingOrderedFarEndpointFamily m n t start target markX targetX) := by
  letI (k : Fin (t + 1)) : Fintype (Fin k) := inferInstance
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype (IsingLineFirstEndpointFamily n k start target) :=
    Fintype.ofFinite _
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (VerticalChoicePathFamily (k - j) markX targetX) :=
    Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - k} :=
    (List.finite_length_eq (Bool × Bool) (t - k)).fintype
  unfold IsingOrderedFarEndpointFamily
  infer_instance


end
end StatMech.Universality
