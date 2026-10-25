/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics.Part5
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCoefficientSemantics


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

@[simp] theorem weightedListEval_nil (weight : Nat -> Real) :
    weightedListEval weight [] = 0 := rfl

@[simp] theorem weightedListEval_cons (weight : Nat -> Real)
    (coefficient : Int) (coefficients : List Int) :
    weightedListEval weight (coefficient :: coefficients) =
      (coefficient : Real) * weight 0 +
        weightedListEval (fun i => weight (i + 1)) coefficients := rfl

theorem updateCoefficient_length (coefficients : List Int) (i : Nat)
    (f : Int -> Int) :
    (updateCoefficient coefficients i f).length = coefficients.length := by
  induction coefficients generalizing i with
  | nil => simp [updateCoefficient]
  | cons coefficient coefficients ih =>
      cases i <;> simp [updateCoefficient, ih]

theorem weightedListEval_update_add (weight : Nat -> Real)
    (coefficients : List Int) (i : Nat) (delta : Int)
    (hi : i < coefficients.length) :
    weightedListEval weight
        (updateCoefficient coefficients i (fun c => c + delta)) =
      weightedListEval weight coefficients + (delta : Real) * weight i := by
  induction coefficients generalizing i weight with
  | nil => simp at hi
  | cons coefficient coefficients ih =>
      cases i with
      | zero =>
          simp [updateCoefficient, weightedListEval]
          ring
      | succ i =>
          have hi' : i < coefficients.length := by simpa using hi
          simp only [updateCoefficient, weightedListEval]
          rw [ih (fun j => weight (j + 1)) i hi']
          push_cast
          ring

theorem weightedListEval_foldl_update
    {alpha : Type*} (weight : Nat -> Real) (xs : List alpha)
    (coefficients : List Int) (index : alpha -> Nat)
    (delta : alpha -> Int)
    (hindex : ∀ x ∈ xs, index x < coefficients.length) :
    weightedListEval weight
        (xs.foldl (fun out x =>
          updateCoefficient out (index x) (fun c => c + delta x))
          coefficients) =
      weightedListEval weight coefficients +
        (xs.map fun x => (delta x : Real) * weight (index x)).sum := by
  induction xs generalizing coefficients with
  | nil => simp
  | cons x xs ih =>
      have hx : index x < coefficients.length := hindex x (by simp)
      have htail : ∀ y ∈ xs,
          index y <
            (updateCoefficient coefficients (index x)
              (fun c => c + delta x)).length := by
        intro y hy
        rw [updateCoefficient_length]
        exact hindex y (by simp [hy])
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih _ htail,
        weightedListEval_update_add weight coefficients (index x)
          (delta x) hx]
      ring

theorem weightedListEval_replicate_zero (weight : Nat -> Real) (n : Nat) :
    weightedListEval weight (List.replicate n 0) = 0 := by
  induction n generalizing weight with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, weightedListEval_cons, ih]
      norm_num

theorem weightedListEval_eq_sum_getD (weight : Nat -> Real)
    (coefficients : List Int) :
    weightedListEval weight coefficients =
      ∑ i ∈ Finset.range coefficients.length,
        (coefficients.getD i 0 : Real) * weight i := by
  induction coefficients generalizing weight with
  | nil => simp
  | cons coefficient coefficients ih =>
      rw [weightedListEval_cons, ih]
      simp only [List.length_cons, Finset.sum_range_succ',
        List.getD_cons_zero,
        List.getD_cons_succ]
      ring

theorem foldl_length_of_step {alpha : Type*} (xs : List alpha)
    (step : List Int -> alpha -> List Int) (coefficients : List Int)
    (hstep : ∀ out x, (step out x).length = out.length) :
    (xs.foldl step coefficients).length = coefficients.length := by
  induction xs generalizing coefficients with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      exact hstep coefficients x

theorem foldl_length_of_invariant {alpha : Type*} (xs : List alpha)
    (step : List Int -> alpha -> List Int) (coefficients : List Int) (n : Nat)
    (hlength : coefficients.length = n)
    (hstep : ∀ out x, out.length = n -> (step out x).length = n) :
    (xs.foldl step coefficients).length = n := by
  induction xs generalizing coefficients with
  | nil => exact hlength
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact ih _ (hstep coefficients x hlength)

theorem weightedListEval_foldl_additive {alpha : Type*}
    (weight : Nat -> Real) (xs : List alpha)
    (step : List Int -> alpha -> List Int) (contribution : alpha -> Real)
    (coefficients : List Int)
    (hstep : ∀ out x, weightedListEval weight (step out x) =
      weightedListEval weight out + contribution x) :
    weightedListEval weight (xs.foldl step coefficients) =
      weightedListEval weight coefficients +
        (xs.map contribution).sum := by
  induction xs generalizing coefficients with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, hstep]
      simp only [List.map_cons, List.sum_cons]
      ring

theorem weightedListEval_foldl_additive_of_length {alpha : Type*}
    (weight : Nat -> Real) (xs : List alpha)
    (step : List Int -> alpha -> List Int) (contribution : alpha -> Real)
    (valid : alpha -> Prop) (coefficients : List Int) (n : Nat)
    (hlength : coefficients.length = n)
    (hvalid : ∀ x ∈ xs, valid x)
    (hstepLength : ∀ out x, out.length = n -> (step out x).length = n)
    (hstepEval : ∀ out x, valid x -> out.length = n ->
      weightedListEval weight (step out x) =
        weightedListEval weight out + contribution x) :
    weightedListEval weight (xs.foldl step coefficients) =
      weightedListEval weight coefficients +
        (xs.map contribution).sum := by
  induction xs generalizing coefficients with
  | nil => simp
  | cons x xs ih =>
      have hnext : (step coefficients x).length = n := by
        exact hstepLength coefficients x hlength
      have hx : valid x := hvalid x (by simp)
      have htail : ∀ y ∈ xs, valid y := by
        intro y hy
        exact hvalid y (by simp [hy])
      rw [List.foldl_cons, ih _ hnext htail,
        hstepEval _ _ hx hlength]
      simp only [List.map_cons, List.sum_cons]
      ring

theorem list_range_sum_eq_finset_range_sum
    (f : Nat -> Real) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem weightedListEval_eq_list_sum_getD (weight : Nat -> Real)
    (coefficients : List Int) :
    weightedListEval weight coefficients =
      ((List.range coefficients.length).map fun i =>
        (coefficients.getD i 0 : Real) * weight i).sum := by
  rw [weightedListEval_eq_sum_getD,
    list_range_sum_eq_finset_range_sum]

theorem list_range_mul_sum_blocks (f : Nat -> Real)
    (blocks width : Nat) :
    ((List.range (blocks * width)).map f).sum =
      ((List.range blocks).map fun block =>
        ((List.range width).map fun offset =>
          f (block * width + offset)).sum).sum := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
      rw [Nat.succ_mul, List.range_add, List.map_append,
        List.sum_append, ih]
      simp [List.range_succ, Function.comp_def]

theorem list_range_add_sum (f : Nat -> Real) (m n : Nat) :
    ((List.range (m + n)).map f).sum =
      ((List.range m).map f).sum +
        ((List.range n).map fun i => f (m + i)).sum := by
  rw [List.range_add, List.map_append, List.sum_append]
  simp [Function.comp_def]

end StatMech.FrontierA.NOneSymmetricMeanCertificate
