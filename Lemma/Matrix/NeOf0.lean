import Mathlib
import Initialize.Tactic.Attr.Basic
import Syntax.LinearAlgebra.Matrix.Notation
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


variable {𝕜 : Type*} [Field 𝕜] {X : Type*}
private lemma det_eval_snoc
  {n : ℕ} (f : Fin (n + 1) → X → 𝕜) (x' : Fin n → X) (y : X) :
  ([i < n + 1, j < n + 1] f j (Fin.snoc (α := fun _ => X) x' y i)).det =
    ∑ j : Fin (n + 1), ((-1 : 𝕜) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
      ([i < n, k < n] f (j.succAbove k) (x' i)).det) * f j y := by
  rw [Matrix.det_succ_row _ (Fin.last n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ([i < n + 1, j < n + 1] f j (Fin.snoc (α := fun _ => X) x' y i)) (Fin.last n) j = f j y := by
    simp [Fin.snoc_last]
  have h2 : ([i < n + 1, j < n + 1] f j (Fin.snoc (α := fun _ => X) x' y i)).submatrix (Fin.last n).succAbove j.succAbove =
      [i < n, k < n] f (j.succAbove k) (x' i) := by
    ext i k
    simp [Matrix.submatrix_apply, Fin.succAbove_last, Fin.snoc_castSucc]
  rw [h1, h2]
  ring
private lemma exists_det_ne_zero
  {n : ℕ} (f : Fin n → X → 𝕜) (hf : LinearIndependent 𝕜 f) :
  ∃ x : Fin n → X, ([i < n, j < n] f j (x i)).det ≠ 0 := by
  induction n
  · refine ⟨Fin.elim0, by simp [Matrix.det_fin_zero]⟩
  ·
    rename_i n ih
    have hf' : LinearIndependent 𝕜 (fun j : Fin n => f (Fin.castSucc j)) :=
      hf.comp _ (Fin.castSucc_injective n)
    obtain ⟨x', hx'⟩ := ih (fun j : Fin n => f (Fin.castSucc j)) hf'
    let c : Fin (n + 1) → 𝕜 := fun j => (-1 : 𝕜) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
      ([i < n, k < n] f (j.succAbove k) (x' i)).det
    have hclast : c (Fin.last n) ≠ 0 := by
      show (-1 : 𝕜) ^ ((Fin.last n : ℕ) + ((Fin.last n : Fin (n + 1)) : ℕ)) *
        ([i < n, k < n] f ((Fin.last n).succAbove k) (x' i)).det ≠ 0
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) ?_
      simp only [Fin.succAbove_last]
      refine hx'
    by_contra hall
    push Not at hall
    have hsum : ∑ j : Fin (n + 1), c j • f j = 0 := by
      funext y
      have this := hall (Fin.snoc (α := fun _ => X) x' y)
      rw [det_eval_snoc] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      refine this
    refine hclast (Fintype.linearIndependent_iff.1 hf c hsum (Fin.last n))
private lemma exists_det_ne_zero_fintype
  {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → X → 𝕜)
  (hf : LinearIndependent 𝕜 f) :
  ∃ x : ι → X, (Matrix.of fun i j : ι => f j (x i)).det ≠ 0 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hf' : LinearIndependent 𝕜 (fun k : Fin (Fintype.card ι) => f (e.symm k)) :=
    hf.comp _ e.symm.injective
  obtain ⟨x, hx⟩ := exists_det_ne_zero (fun k : Fin (Fintype.card ι) => f (e.symm k)) hf'
  refine ⟨fun i => x (e i), ?_⟩
  have h : (Matrix.of fun i j : ι => f j (x (e i))) =
      ([k < Fintype.card ι, l < Fintype.card ι] f (e.symm l) (x k)).submatrix e e := by
    ext i j
    simp [Matrix.submatrix_apply]
  rw [h, Matrix.det_submatrix_equiv_self]
  refine hx
/--
[exists_det_of_apply_ne_zero_of_linearIndependent](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_exists_det_of_apply_ne_zero_of_linearIndependent.lean)
-/
@[path]
private lemma main
  [Fintype ι] [DecidableEq ι]
  {f : ι → X → 𝕜}
-- given
  (hf : LinearIndependent 𝕜 f) :
-- imply
  ∃ x : ι → X, (Matrix.of fun i j : ι => f j (x i)).det ≠ 0 :=
  exists_det_ne_zero_fintype f hf


-- created on 2026-10-20
-- updated on 2026-10-27
