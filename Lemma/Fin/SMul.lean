import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
private lemma base
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ENat) φ) (A : E → F) (hA : ContDiff ℝ (⊤ : ENat) A)
  (j : ℕ) (e : E) (ρ : ℝ) (u : Fin j → E) :
  iteratedFDeriv ℝ j (fun p : E × ℝ => φ p.2 • A p.1) (e, ρ) (fun i => ((u i, 0) : E × ℝ)) =
    φ ρ • iteratedFDeriv ℝ j A e u := by
  obtain ⟨P, hP⟩ : ∃ P : E × ℝ → F, P = fun p : E × ℝ => φ p.2 • A p.1 := ⟨_, rfl⟩
  rw [← hP]
  let inl : E →L[ℝ] E × ℝ := ContinuousLinearMap.inl ℝ E ℝ
  have hG : ContDiff ℝ (⊤ : ENat) (fun p : E × ℝ => P (p + ((0 : E), ρ))) := by
    rw [hP]
    refine ((hφ.comp contDiff_snd).smul (hA.comp contDiff_fst)).comp (contDiff_id.add contDiff_const)
  have hcomp : (fun p : E × ℝ => P (p + ((0 : E), ρ))) ∘ inl = fun x : E => φ ρ • A x := by
    funext x
    rw [hP]
    simp [inl]
  calc
    _ = (iteratedFDeriv ℝ j P (inl e + ((0 : E), ρ))).compContinuousLinearMap (fun _ => inl) u := by
      simp [inl, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    _ = (iteratedFDeriv ℝ j (fun p : E × ℝ => P (p + ((0 : E), ρ))) (inl e)).compContinuousLinearMap (fun _ => inl) u := by
      rw [iteratedFDeriv_comp_add_right]
    _ = iteratedFDeriv ℝ j ((fun p : E × ℝ => P (p + ((0 : E), ρ))) ∘ inl) e u := by
      rw [ContinuousLinearMap.iteratedFDeriv_comp_right inl hG e (by exact_mod_cast le_top)]
    _ = iteratedFDeriv ℝ j (fun x : E => φ ρ • A x) e u := by
      rw [hcomp]
    _ = φ ρ • iteratedFDeriv ℝ j A e u := by
      rw [iteratedFDeriv_const_smul_apply' (hA.contDiffAt.of_le (by exact_mod_cast le_top))]
      rfl
private lemma fderiv_apply_inr
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ENat) φ) (A : E → F) (hA : ContDiff ℝ (⊤ : ENat) A)
  (y : E × ℝ) :
  fderiv ℝ (fun p : E × ℝ => φ p.2 • A p.1) y ((0 : E), (1 : ℝ)) = deriv φ y.2 • A y.1 := by
  have hc : DifferentiableAt ℝ (fun p : E × ℝ => φ p.2) y :=
    ((hφ.differentiable (by simp)).differentiableAt).comp y differentiableAt_snd
  have hf : DifferentiableAt ℝ (fun p : E × ℝ => A p.1) y :=
    ((hA.differentiable (by simp)).differentiableAt).comp y differentiableAt_fst
  have h := fderiv_smul hc hf
  rw [show (fun p : E × ℝ => φ p.2 • A p.1) = (fun p : E × ℝ => φ p.2) • (fun p : E × ℝ => A p.1) from rfl, h]
  rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have h1 : fderiv ℝ (fun p : E × ℝ => A p.1) y ((0 : E), (1 : ℝ)) = 0 := by
    rw [show (fun p : E × ℝ => A p.1) = A ∘ Prod.fst from rfl,
      fderiv_comp y ((hA.differentiable (by simp)).differentiableAt) differentiableAt_fst, fderiv_fst]
    simp
  have h2 : fderiv ℝ (fun p : E × ℝ => φ p.2) y ((0 : E), (1 : ℝ)) = deriv φ y.2 := by
    rw [show (fun p : E × ℝ => φ p.2) = φ ∘ Prod.snd from rfl,
      fderiv_comp y ((hφ.differentiable (by simp)).differentiableAt) differentiableAt_snd, fderiv_snd]
    simp
  rw [h1, h2, smul_zero, zero_add]
private lemma helper_main
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ENat) φ) (A : E → F) (hA : ContDiff ℝ (⊤ : ENat) A)
  (j l : ℕ) (e : E) (ρ : ℝ) (u : Fin j → E) :
  iteratedFDeriv ℝ (j + l) (fun p : E × ℝ => φ p.2 • A p.1) (e, ρ)
      (Fin.append (fun i => ((u i, 0) : E × ℝ)) (fun _ : Fin l => ((0, 1) : E × ℝ))) =
    iteratedDeriv l φ ρ • iteratedFDeriv ℝ j A e u := by
  induction l generalizing φ ρ
  ·
    have hv : (Fin.append (fun i => ((u i, 0) : E × ℝ)) (fun _ : Fin 0 => ((0, 1) : E × ℝ)) : Fin (j + 0) → E × ℝ) =
        fun i : Fin j => ((u i, 0) : E × ℝ) := by
      rw [show (fun _ : Fin 0 => ((0, 1) : E × ℝ)) = Fin.elim0 from funext fun i => i.elim0, Fin.append_elim0]
      rfl
    rw [iteratedDeriv_zero]
    show iteratedFDeriv ℝ j (fun p : E × ℝ => φ p.2 • A p.1) (e, ρ)
      (Fin.append (fun i => ((u i, 0) : E × ℝ)) (fun _ : Fin 0 => ((0, 1) : E × ℝ))) = _
    rw [hv]
    refine base φ hφ A hA j e ρ u
  ·
    rename_i l ih
    have hP : ContDiff ℝ (⊤ : ENat) (fun p : E × ℝ => φ p.2 • A p.1) :=
      (hφ.comp contDiff_snd).smul (hA.comp contDiff_fst)
    have hφ' : ContDiff ℝ (⊤ : ENat) (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    show iteratedFDeriv ℝ (j + l + 1) (fun p : E × ℝ => φ p.2 • A p.1) (e, ρ)
      (Fin.append (m := j) (n := l + 1) (fun i : Fin j => ((u i, 0) : E × ℝ)) (fun _ : Fin (l + 1) => ((0, 1) : E × ℝ))) = _
    rw [iteratedFDeriv_succ_apply_right]
    have hsn : (fun _ : Fin (l + 1) => ((0, 1) : E × ℝ)) = Fin.snoc (fun _ : Fin l => ((0, 1) : E × ℝ)) ((0, 1) : E × ℝ) := by
      funext i
      simp only [Fin.snoc]
      split_ifs
      · rfl
      · rfl
    rw [hsn, Fin.append_snoc, Fin.init_snoc]
    erw [Fin.snoc_last]
    have hev : ∀ w : Fin (j + l) → E × ℝ,
        iteratedFDeriv ℝ (j + l) (fun y => fderiv ℝ (fun p : E × ℝ => φ p.2 • A p.1) y) (e, ρ) w ((0 : E), (1 : ℝ)) =
          iteratedFDeriv ℝ (j + l) (fun y => fderiv ℝ (fun p : E × ℝ => φ p.2 • A p.1) y ((0 : E), (1 : ℝ))) (e, ρ) w := by
      intro w
      have hfd : ContDiff ℝ (⊤ : ENat) (fderiv ℝ (fun p : E × ℝ => φ p.2 • A p.1)) :=
        hP.fderiv_right (by exact_mod_cast le_top)
      have := ContinuousLinearMap.iteratedFDeriv_comp_left (ContinuousLinearMap.apply ℝ F ((0 : E), (1 : ℝ)))
        (hfd.contDiffAt (x := (e, ρ))) (i := j + l) (by exact_mod_cast le_top)
      rw [show (⇑(ContinuousLinearMap.apply ℝ F ((0 : E), (1 : ℝ))) ∘ fderiv ℝ (fun p : E × ℝ => φ p.2 • A p.1)) =
        fun y => fderiv ℝ (fun p : E × ℝ => φ p.2 • A p.1) y ((0 : E), (1 : ℝ)) from rfl] at this
      rw [this]
      rfl
    rw [hev]
    have hfun : (fun y : E × ℝ => fderiv ℝ (fun p : E × ℝ => φ p.2 • A p.1) y ((0 : E), (1 : ℝ))) =
        fun p : E × ℝ => deriv φ p.2 • A p.1 := funext fun y => fderiv_apply_inr φ hφ A hA y
    rw [hfun, ih (deriv φ) hφ' ρ, iteratedDeriv_succ']
/--
[iteratedFDeriv_smul_comp_apply_append_inl_inr](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_iteratedFDeriv_smul_comp_apply_append_inl_inr.lean)
-/
@[path]
private lemma main
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ENat) φ) (A : E → F) (hA : ContDiff ℝ (⊤ : ENat) A)
  (j l : ℕ) (e : E) (ρ : ℝ) (u : Fin j → E) :
  -- imply
  iteratedFDeriv ℝ (j + l) (fun p : E × ℝ => φ p.2 • A p.1) (e, ρ)
      (Fin.append (fun i => ((u i, 0) : E × ℝ)) (fun _ : Fin l => ((0, 1) : E × ℝ))) =
    iteratedDeriv l φ ρ • iteratedFDeriv ℝ j A e u := by
  -- proof
  refine helper_main φ hφ A hA j l e ρ u


-- created on 2026-10-21
