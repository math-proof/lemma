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
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem isingLeapfrogChoiceRun_of_boundary_endpointFailure
    (R : Nat) (p : IsingLeapfrogBox R)
    (hp : isingLeapfrogBoxBoundary R p) (bs : List (Bool × Bool)) :
    isingLeapfrogChoiceRun R p bs = p := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [isingLeapfrogChoiceRun]
      rw [show isingLeapfrogChoiceNext R p b = p by
        simp [isingLeapfrogChoiceNext, hp]]
      exact ih

theorem prodBits_zip_self_endpointFailure
    (bs : List (Bool × Bool)) :
    (bs.map Prod.fst).zip (bs.map Prod.snd) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [ih]

theorem map_fst_zip_of_length_eq_endpointFailure
    (xs ys : List Bool) (h : xs.length = ys.length) :
    (xs.zip ys).map Prod.fst = xs := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp [ih ys h]

theorem map_snd_zip_of_length_eq_endpointFailure
    (xs ys : List Bool) (h : xs.length = ys.length) :
    (xs.zip ys).map Prod.snd = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp [ih ys h]

theorem lineFreeEndpoint_append_endpointFailure
    (start : Int) (a b : List Bool) :
    lineFreeEndpoint start (a ++ b) =
      lineFreeEndpoint (lineFreeEndpoint start a) b := by
  induction a generalizing start with
  | nil => rfl
  | cons x a ih =>
      cases x <;> simp only [List.cons_append, lineFreeEndpoint] <;>
        exact ih _

end
end StatMech.Universality
