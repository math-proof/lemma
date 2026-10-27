import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.EuclideanSymplectic
open EuclideanΩ


/--
[standardSymplecticForm_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanSymplectic.lean)
-/
@[path]
lemma standardSymplecticForm_closed
  {n : ℕ} :
-- imply
  euclideanD_lifted (standardSymplecticForm n) = 0 := by
-- proof
  unfold euclideanD_lifted standardSymplecticForm toCEuclideanΩ
  ext x v
  simp only [euclideanD, AlternatingMap.alternatizeUncurryFin_apply, EuclideanΩ.zero_apply',
    AlternatingMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hconst : fderiv ℝ (fun (_ : Eℝ (2 * n)) => toCAlt (standardSymplecticAlt n)) x = 0 := by
    have : (fun (_ : Eℝ (2 * n)) => toCAlt (standardSymplecticAlt n)) =
      Function.const _ (toCAlt (standardSymplecticAlt n)) := rfl
    rw [this]
    exact congr_fun (fderiv_const (toCAlt (standardSymplecticAlt n))) x
  unfold fderivToAltMap
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hconst,
    ContinuousLinearMap.zero_apply, map_zero, AlternatingMap.zero_apply, smul_zero]

/--
[standardSymplecticBilinear_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanSymplectic.lean)
-/
@[path]
lemma standardSymplecticBilinear_nondegenerate
  {n : ℕ}
  {u : Eℝ (2 * n)}
-- given
  (h : ∀ v : Eℝ (2 * n), (∑ i : Fin n, (u ⟨i.val, by omega⟩ * v ⟨n + i.val, by omega⟩ - u ⟨n + i.val, by omega⟩ * v ⟨i.val, by omega⟩)) = 0) :
-- imply
  u = 0 := by
-- proof
  ext ⟨k, hk⟩
  simp only [PiLp.zero_apply]
  by_cases hkn : k < n
  ·
    have htest := h (EuclideanSpace.single ⟨n + k, by omega⟩ 1)
    simp only [PiLp.single_apply] at htest
    rw [Finset.sum_eq_single ⟨k, hkn⟩] at htest
    · simp only [ite_true, mul_one] at htest
      have hne : ¬(⟨k, by omega⟩ : Fin (2 * n)) = ⟨n + k, by omega⟩ :=
        Fin.ne_of_val_ne (by dsimp; omega)
      simp only [hne, ite_false, mul_zero, sub_zero] at htest
      exact htest
    · intro i _ hi
      have : ¬(⟨n + i.val, by omega⟩ : Fin (2 * n)) = ⟨n + k, by omega⟩ := by
        intro heq; exact hi (Fin.ext (by simpa using Fin.val_eq_of_eq heq))
      simp only [this, ite_false, mul_zero]
      have : ¬(⟨i.val, by omega⟩ : Fin (2 * n)) = ⟨n + k, by omega⟩ :=
        Fin.ne_of_val_ne (by dsimp; omega)
      simp only [this, ite_false, mul_zero, sub_zero]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  ·
    push Not at hkn
    have hk' : k - n < n := by omega
    have htest := h (EuclideanSpace.single ⟨k - n, by omega⟩ 1)
    simp only [PiLp.single_apply] at htest
    rw [Finset.sum_eq_single ⟨k - n, hk'⟩] at htest
    · have hne : ¬(⟨n + (k - n), by omega⟩ : Fin (2 * n)) = ⟨k - n, by omega⟩ :=
      Fin.ne_of_val_ne (by dsimp; omega)
      simp only [hne, ite_false, mul_zero, zero_sub, neg_eq_zero] at htest
      simp only [ite_true, mul_one] at htest
      have hkk : (⟨k, hk⟩ : Fin (2 * n)) = ⟨n + (k - n), by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rwa [hkk]
    · intro i _ hi
      have hne1 : ¬(⟨i.val, by omega⟩ : Fin (2 * n)) = ⟨k - n, by omega⟩ := by
        intro heq; exact hi (Fin.ext (by simpa using Fin.val_eq_of_eq heq))
      simp only [hne1, ite_false, mul_zero, sub_zero]
      have hne2 : ¬(⟨n + i.val, by omega⟩ : Fin (2 * n)) = ⟨k - n, by omega⟩ :=
        Fin.ne_of_val_ne (by dsimp; omega)
      simp only [hne2, ite_false, mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem

/--
[standardSymplecticForm_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanSymplectic.lean)
-/
@[path]
lemma standardSymplecticForm_nondegenerate
  {n : ℕ} :
-- imply
  Function.Injective (fun (X : EuclideanVF (2 * n)) => euclideanIota X (standardSymplecticForm n)) := by
-- proof
  intro X Y h
  funext x
  suffices hdiff : X x - Y x = 0 from sub_eq_zero.mp hdiff
  apply standardSymplecticBilinear_nondegenerate n
  intro v
  have hpt : euclideanIota X (standardSymplecticForm n) x =
    euclideanIota Y (standardSymplecticForm n) x := by
    have := congr_fun h x
    simp only at this
    exact this
  have key : (standardSymplecticAlt n).curryLeft (X x) =
    (standardSymplecticAlt n).curryLeft (Y x) := by
    have : euclideanIota X (standardSymplecticForm n) x =
      euclideanIota Y (standardSymplecticForm n) x := hpt
    simp only [euclideanIota, standardSymplecticForm] at this
    exact this
  have h_map_sub : (standardSymplecticAlt n).curryLeft (X x - Y x) =
    (standardSymplecticAlt n).curryLeft (X x) -
    (standardSymplecticAlt n).curryLeft (Y x) :=
    map_sub (standardSymplecticAlt n).curryLeft (X x) (Y x)
  have h_zero : (standardSymplecticAlt n).curryLeft (X x - Y x) = 0 := by
    rw [h_map_sub, key, sub_self]
  have h_eval : ∀ w : Fin 1 → Eℝ (2 * n),
    (standardSymplecticAlt n).curryLeft (X x - Y x) w = 0 := by
    intro w; rw [h_zero]; rfl
  have h_sum := h_eval (fun _ => v)
  simp only [AlternatingMap.curryLeft_apply_apply, standardSymplecticAlt,
    AlternatingMap.coe_mk, MultilinearMap.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h_sum
  exact h_sum

/--
[Fin2_eq_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanSymplectic.lean)
-/
@[path]
private lemma Fin2_eq_zero_or_one_eq
  {k : Fin 2} :
-- imply
  k = 0 ∨ k = 1 := by
-- proof
  apply Fin2_eq_zero_or_one k


-- created on 2026-10-23
