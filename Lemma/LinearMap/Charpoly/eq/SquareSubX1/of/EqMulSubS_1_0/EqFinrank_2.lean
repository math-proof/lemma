import Mathlib
import Initialize.Tactic.Attr.Basic
open LinearMap


private lemma trace_eq_zero_of_mul_self_eq_zero_fin_two {A : Type u} [CommRing A] [IsDomain A]
  (N : Matrix (Fin 2) (Fin 2) A) (hN : N * N = 0) : N.trace = 0 ∧ N.det = 0 := by
  have e : ∀ i j, N i 0 * N 0 j + N i 1 * N 1 j = 0 := fun i j => by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hN i) j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  if h : N 0 0 + N 1 1 = 0 then
    exact ⟨h, by linear_combination N 0 0 * h - e 0 0⟩
  else
    exfalso
    have hb : N 0 1 = 0 :=
      (mul_eq_zero.mp (by linear_combination e 0 1 : N 0 1 * (N 0 0 + N 1 1) = 0)).resolve_right h
    have hc : N 1 0 = 0 :=
      (mul_eq_zero.mp (by linear_combination e 1 0 : N 1 0 * (N 0 0 + N 1 1) = 0)).resolve_right h
    have ha : N 0 0 = 0 := mul_self_eq_zero.mp (by linear_combination e 0 0 - N 1 0 * hb)
    have hd : N 1 1 = 0 := mul_self_eq_zero.mp (by linear_combination e 1 1 - N 0 1 * hc)
    refine h (by rw [ha, hd, add_zero])
open Polynomial in

private lemma matrix_charpoly_eq {A : Type u} [CommRing A] [IsDomain A]
  (M : Matrix (Fin 2) (Fin 2) A) (hM : (M - 1) * (M - 1) = 0) : M.charpoly = (X - 1) ^ 2 := by
  obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, (sub_add_cancel M 1).symm⟩
  rw [add_sub_cancel_right] at hM
  obtain ⟨htr, hdet⟩ := trace_eq_zero_of_mul_self_eq_zero_fin_two N hM
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have htr' : (N + 1).trace = 2 := by
    rw [Matrix.trace_add, Matrix.trace_fin_two, htr, Matrix.trace_one, Fintype.card_fin, zero_add, Nat.cast_ofNat]
  have hdet' : (N + 1).det = 1 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
    linear_combination hdet + htr
  rw [Matrix.charpoly_fin_two, htr', hdet', _root_.map_ofNat, _root_.map_one]
  ring

open Polynomial in

private lemma linearMap_charpoly_eq {A : Type u} [CommRing A] [IsDomain A] {V : Type v} [AddCommGroup V] [Module A V]
  [Module.Free A V] [Module.Finite A V] (hV : Module.finrank A V = 2)
  (f : Module.End A V) (hf : (f - 1) * (f - 1) = 0) : f.charpoly = (X - 1) ^ 2 := by
  let b := Module.finBasisOfFinrankEq A V hV
  rw [← LinearMap.charpoly_toMatrix f b]
  refine matrix_charpoly_eq _ ?_
  have h := congrArg (LinearMap.toMatrix b b) hf
  rwa [LinearMap.toMatrix_mul, _root_.map_sub, LinearMap.toMatrix_one, _root_.map_zero] at h
/--
[LinearMap_charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A] [IsDomain A]
  {V : Type v} [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]
  {f : Module.End A V}
-- given
  (hV : Module.finrank A V = 2)
  (hf : (f - 1) * (f - 1) = 0) :
-- imply
  LinearMap.charpoly f = (Polynomial.X - 1) ^ 2 :=
-- proof
  linearMap_charpoly_eq hV f hf


-- created on 2026-10-23
