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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part16


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def orderedFarEndpointValue
    (m n t : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) :
    IsingOrderedFarEndpointFamily m n t start target markX targetX ->
      IsingLeapfrogChoiceStringFamily t := fun z => by
  let xs := z.2.2.1.1 ++ z.2.2.2.2.1.1 ++ z.2.2.2.2.2.1.map Prod.fst
  let ys := z.2.2.2.1.1 ++ z.2.2.2.2.2.1.map Prod.snd
  refine ⟨xs.zip ys, ?_⟩
  have hx : xs.length = t := by
    dsimp [xs]
    rw [List.length_append, List.length_append, List.length_map,
      z.2.2.1.2.1, z.2.2.2.2.1.2.1, z.2.2.2.2.2.2]
    omega
  have hy : ys.length = t := by
    dsimp [ys]
    rw [List.length_append, List.length_map,
      z.2.2.2.1.2.1, z.2.2.2.2.2.2]
    omega
  rw [List.length_zip, hx, hy, min_self]

def IsingOrderedFarHorizontalEndpointFamily
    (m R t : Nat) (mark target : IsingLineBox R)
    (startY targetY : Int) :=
  Sigma fun k : Fin (t + 1) =>
    Sigma fun j : Fin k =>
      IsingLineFarFirstBoundaryFamily m j ×
        IsingLineFirstEndpointFamily R (k - j) mark target ×
        VerticalChoicePathFamily k startY targetY ×
        {tail : List (Bool × Bool) // tail.length = t - k}

def orderedFarHorizontalEndpointValue
    (m R t : Nat) (mark target : IsingLineBox R)
    (startY targetY : Int) :
    IsingOrderedFarHorizontalEndpointFamily m R t mark target startY targetY ->
      IsingLeapfrogChoiceStringFamily t := fun z => by
  let xs := z.2.2.1.1 ++ z.2.2.2.1.1 ++ z.2.2.2.2.2.1.map Prod.fst
  let ys := z.2.2.2.2.1.1 ++ z.2.2.2.2.2.1.map Prod.snd
  refine ⟨xs.zip ys, ?_⟩
  have hx : xs.length = t := by
    dsimp [xs]
    rw [List.length_append, List.length_append, List.length_map,
      z.2.2.1.2.1, z.2.2.2.1.2.1, z.2.2.2.2.2.2]
    omega
  have hy : ys.length = t := by
    dsimp [ys]
    rw [List.length_append, List.length_map,
      z.2.2.2.2.1.2.1, z.2.2.2.2.2.2]
    omega
  rw [List.length_zip, hx, hy, min_self]

end
end StatMech.Universality
