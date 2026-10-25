/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part29


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareSignedEighthTurn_congr
    {a b c d : Int} (ha : a ≡ b [ZMOD 8]) (hc : c ≡ d [ZMOD 8]) :
    fkIsingSquareSignedEighthTurn a c =
      fkIsingSquareSignedEighthTurn b d := by
  have h := (hc.sub ha).add (Int.ModEq.refl 4)
  unfold Int.ModEq at h
  unfold fkIsingSquareSignedEighthTurn
  rw [h]

theorem carrierAdjacentSum_flatMap
    {A B : Type*} (turn : B → B → Int)
    (code : A → List B) (hcode : ∀ a, code a ≠ []) (l : List A) :
    carrierAdjacentSum turn (l.flatMap code) =
      carrierAdjacentSum
          (fun a b => turn ((code a).getLast (hcode a))
            ((code b).head (hcode b))) l +
        (l.map fun a => carrierAdjacentSum turn (code a)).sum := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b tail =>
          have hrest : (code b ++ tail.flatMap code) ≠ [] := by
            exact List.append_ne_nil_of_left_ne_nil (hcode b) _
          change carrierAdjacentSum turn
              (code a ++ (code b ++ tail.flatMap code)) = _
          rw [carrierAdjacentSum_append turn (code a)
            (code b ++ tail.flatMap code) (hcode a) hrest]
          have ih' :
              carrierAdjacentSum turn (code b ++ tail.flatMap code) =
                carrierAdjacentSum
                    (fun a b => turn ((code a).getLast (hcode a))
                      ((code b).head (hcode b))) (b :: tail) +
                  ((b :: tail).map fun a =>
                    carrierAdjacentSum turn (code a)).sum := by
            simpa only [List.flatMap_cons] using ih
          rw [ih']
          simp only [List.map_cons, List.sum_cons,
            carrierAdjacentSum_cons_cons]
          have hhead : (code b ++ tail.flatMap code).head hrest =
              (code b).head (hcode b) := by
            simp [List.head_append, hcode b]
          rw [hhead]
          omega

theorem carrierAdjacentSum_chain_congr
    {A : Type*} (left right : A → A → Int) (l : List A)
    (hchain : l.Chain' fun a b => left a b = right a b) :
    carrierAdjacentSum left l = carrierAdjacentSum right l := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => rfl
      | cons b tail =>
          rw [carrierAdjacentSum_cons_cons, carrierAdjacentSum_cons_cons]
          rw [hchain.rel]
          rw [ih hchain.tail]

theorem carrierAdjacentSum_snd_add_head_eq_sum
    {A : Type*} (value : A → Int) (l : List A) (hl : l ≠ []) :
    carrierAdjacentSum (fun _ b => value b) l + value (l.head hl) =
      (l.map value).sum := by
  induction l with
  | nil => exact False.elim (hl rfl)
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b tail =>
          rw [carrierAdjacentSum_cons_cons]
          simp only [List.head_cons, List.map_cons, List.sum_cons]
          have hne : b :: tail ≠ [] := by simp
          have hi := ih hne
          simp only [List.head_cons, List.map_cons, List.sum_cons] at hi
          omega

theorem carrierAdjacentSum_fst_add_last_eq_sum
    {A : Type*} (value : A → Int) (l : List A) (hl : l ≠ []) :
    carrierAdjacentSum (fun a _ => value a) l + value (l.getLast hl) =
      (l.map value).sum := by
  induction l with
  | nil => exact False.elim (hl rfl)
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b tail =>
          rw [carrierAdjacentSum_cons_cons]
          have hne : b :: tail ≠ [] := by simp
          rw [List.getLast_cons hne]
          simp only [List.map_cons, List.sum_cons]
          have hi := ih hne
          simp only [List.map_cons, List.sum_cons] at hi
          omega

theorem List.sum_map_modEq
    {A : Type*} {f g : A → Int} (l : List A) (m : Int)
    (h : ∀ a ∈ l, f a ≡ g a [ZMOD m]) :
    (l.map f).sum ≡ (l.map g).sum [ZMOD m] := by
  induction l with
  | nil => exact Int.ModEq.refl 0
  | cons a tail ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (h a (by simp)).add (ih (fun b hb => h b (by simp [hb])))

theorem List.sum_map_add_sub
    {A : Type*} (l : List A) (f g h : A → Int) :
    (l.map fun a => f a + g a - h a).sum =
      (l.map f).sum + (l.map g).sum - (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a tail ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem List.chain'_iterate
    {A : Type*} (f : A → A) (d : A) (k : Nat) :
    (List.iterate f d k).Chain' fun q r => r = f q := by
  induction k generalizing d with
  | zero => exact List.IsChain.nil
  | succ k ih =>
      cases k with
      | zero => exact List.IsChain.singleton d
      | succ k => exact List.IsChain.cons_cons rfl (ih (f d))

end
end StatMech.Universality
