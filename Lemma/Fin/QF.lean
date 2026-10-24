import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusProof
import Lemma.Real.QF.eq.BF
open Finset BigOperators CoxeterGroup PerronFrobeniusProof


/--
[QF_insertNth_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusCorollary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {f : Fin (n + 1) → Fin (n + 1) → ℝ}
  {i₀ : Fin (n + 1)}
  {w : Fin n → ℝ} :
-- imply
  QF f (Fin.insertNth (α := fun _ => ℝ) i₀ (0 : ℝ) w) = QF (fun i j => f (i₀.succAbove i) (i₀.succAbove j)) w := by
-- proof
  simp only [QF]
  rw [Fin.sum_univ_succAbove _ i₀]
  simp only [Fin.insertNth_apply_same, zero_mul, Finset.sum_const_zero, zero_add]
  congr 1; funext s
  rw [Fin.sum_univ_succAbove _ i₀]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]



/--
[restrictForm_offDiag](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusCorollary.lean)
-/
private lemma restrictForm_offDiag
  {n : ℕ}
  {f : Fin (n + 1) → Fin (n + 1) → ℝ}
  {i₀ : Fin (n + 1)}
-- given
  (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0) :
-- imply
  ∀ s t : Fin n, s ≠ t → f (i₀.succAbove s) (i₀.succAbove t) ≤ 0 := by
-- proof
  intro s t hst
  exact hOffDiag _ _ (Fin.succAbove_right_injective.ne hst)



/--
[insertNth_abs_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusCorollary.lean)
-/
private lemma insertNth_abs_ne_zero
  {n : ℕ}
  {i₀ : Fin (n + 1)}
  {w : Fin n → ℝ}
-- given
  (hw : w ≠ 0) :
-- imply
  Fin.insertNth (α := fun _ => ℝ) i₀ (0 : ℝ) (fun k => |w k|) ≠ 0 := by
-- proof
  intro h
  apply hw
  funext k
  have := congr_fun h (i₀.succAbove k)
  simp [Fin.insertNth_apply_succAbove] at this
  exact this



/--
[insertNth_abs_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusCorollary.lean)
-/
private lemma insertNth_abs_nonneg
  {n : ℕ}
  {i₀ : Fin (n + 1)}
  {w : Fin n → ℝ} :
-- imply
  ∀ b, Fin.insertNth (α := fun _ => ℝ) i₀ (0 : ℝ) (fun k => |w k|) b ≥ 0 := by
-- proof
  intro b
  by_cases h : b = i₀
  · simp [h, Fin.insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
    simp [Fin.insertNth_apply_succAbove, abs_nonneg]



/--
[submatrix_positive_definite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusCorollary.lean)
-/
private lemma submatrix_positive_definite
  {n : ℕ}
  {f : Fin (n + 1) → Fin (n + 1) → ℝ}
  {i₀ : Fin (n + 1)}
-- given
  (hPSD : ∀ u : Fin (n + 1) → ℝ, QF f u ≥ 0)
  (hOffDiag : ∀ s t : Fin (n + 1), s ≠ t → f s t ≤ 0)
  (hIndecomp : FormIndecomposable f) :
-- imply
  ∀ w : Fin n → ℝ, w ≠ 0 → QF (fun i j => f (i₀.succAbove i) (i₀.succAbove j)) w > 0 := by
-- proof
  intro w hw
  set g := fun i j => f (i₀.succAbove i) (i₀.succAbove j) with hg_def
  have hOffDiag_g : ∀ s t : Fin n, s ≠ t → g s t ≤ 0 :=
    restrictForm_offDiag f i₀ hOffDiag
  by_contra h_not_pos
  push_neg at h_not_pos
  set v := Fin.insertNth (α := fun _ => ℝ) i₀ (0 : ℝ) (fun k => |w k|) with hv_def
  have hQF_v : QF f v = QF g (fun k => |w k|) := QF_insertNth_zero f i₀ (fun k => |w k|)
  have habs_le : QF g (fun k => |w k|) ≤ QF g w := QF_abs_le g w hOffDiag_g
  have hPSD_v : QF f v ≥ 0 := hPSD v
  have hQF_v_zero : QF f v = 0 := le_antisymm (by linarith) hPSD_v
  have hv_nonneg : ∀ b, v b ≥ 0 := insertNth_abs_nonneg i₀ w
  have hv_ne : v ≠ 0 := insertNth_abs_ne_zero i₀ w hw
  have hv_pos : ∀ b, v b > 0 :=
    nonneg_kernel_pos f v hPSD hQF_v_zero hv_nonneg hv_ne hOffDiag hIndecomp
  have hv_i₀ : v i₀ = 0 := by simp [hv_def, Fin.insertNth_apply_same]
  linarith [hv_pos i₀]



-- created on 2026-10-23
-- updated on 2026-10-24
