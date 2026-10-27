import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma sq_eq [Field 𝕜] (t : Matrix (Fin 2) (Fin 2) 𝕜) : t * t = Matrix.trace t • t - Matrix.det t • (1 : Matrix (Fin 2) (Fin 2) 𝕜) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i
  ·
    fin_cases j
    ·
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    ·
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
  ·
    fin_cases j
    ·
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    ·
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
private lemma conj_eq [Field 𝕜] (t x xinv : Matrix (Fin 2) (Fin 2) 𝕜) (hx : xinv * x = 1) (ht : Matrix.trace t ≠ 0) : xinv * t * x = (Matrix.trace t)⁻¹ • (xinv * (t * t) * x + Matrix.det t • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) := by
  have e : t = (Matrix.trace t)⁻¹ • (t * t + Matrix.det t • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) := by
    rw [sq_eq, sub_add_cancel, smul_smul, inv_mul_cancel₀ ht, one_smul]
  conv_lhs => rw [e]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hx]
private lemma trace_inv_val [Field 𝕜] (t : GL (Fin 2) 𝕜) : Matrix.trace (((t⁻¹ : GL (Fin 2) 𝕜)) : Matrix (Fin 2) (Fin 2) 𝕜) = Matrix.trace ((t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) / Matrix.det ((t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) := by
  have hdet : Matrix.det ((t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 t.isUnit).ne_zero
  have hinv : (((t⁻¹ : GL (Fin 2) 𝕜)) : Matrix (Fin 2) (Fin 2) 𝕜) = ((t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜)⁻¹ := Matrix.coe_units_inv t
  rw [hinv, Matrix.inv_def, Matrix.trace_smul, Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Ring.inverse_eq_inv', smul_eq_mul]
  rw [div_eq_inv_mul, add_comm]
/--
[Matrix_GeneralLinearGroup_exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_GeneralLinearGroup_exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero.lean)
-/
@[path]
private lemma main
  [RCLike 𝕜]
  (T : Set (GL (Fin 2) 𝕜)) (hT : IsCompact T)
  (hTtr : ∀ t ∈ T, Matrix.trace (Units.val t) ≠ 0)
  (B : Set (GL (Fin 2) 𝕜)) (hB : IsCompact B) :
  -- imply
  ∃ B' : Set (GL (Fin 2) 𝕜), IsCompact B' ∧ ∀ t ∈ T, ∀ x : GL (Fin 2) 𝕜, x⁻¹ * (t * t) * x ∈ B → x⁻¹ * t * x ∈ B' := by
  -- proof
  set val : GL (Fin 2) 𝕜 → Matrix (Fin 2) (Fin 2) 𝕜 := fun g => (g : Matrix (Fin 2) (Fin 2) 𝕜) with hval
  have hcval : Continuous val := Units.continuous_val
  have hcinv : Continuous fun g : GL (Fin 2) 𝕜 => g⁻¹ := continuous_inv
  set V : GL (Fin 2) 𝕜 × GL (Fin 2) 𝕜 → Matrix (Fin 2) (Fin 2) 𝕜 := fun p => (Matrix.trace (val p.1))⁻¹ • (val p.2 + Matrix.det (val p.1) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) with hV
  set W : GL (Fin 2) 𝕜 × GL (Fin 2) 𝕜 → Matrix (Fin 2) (Fin 2) 𝕜 := fun p => (Matrix.trace (val p.1⁻¹))⁻¹ • (val p.2⁻¹ + Matrix.det (val p.1⁻¹) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) with hW
  have htr : Continuous fun m : Matrix (Fin 2) (Fin 2) 𝕜 => Matrix.trace m := by
    have : (fun m : Matrix (Fin 2) (Fin 2) 𝕜 => Matrix.trace m) = fun m => m 0 0 + m 1 1 := by
      funext m
      rw [Matrix.trace_fin_two]
    rw [this]
    fun_prop
  have hdetc : Continuous fun m : Matrix (Fin 2) (Fin 2) 𝕜 => Matrix.det m := continuous_id.matrix_det
  have hTtr' : ∀ p ∈ T ×ˢ B, Matrix.trace (val p.1) ≠ 0 := fun p hp => hTtr p.1 hp.1
  have hTtr'' : ∀ p ∈ T ×ˢ B, Matrix.trace (val p.1⁻¹) ≠ 0 := by
    intro p hp
    show Matrix.trace (((p.1⁻¹ : GL (Fin 2) 𝕜)) : Matrix (Fin 2) (Fin 2) 𝕜) ≠ 0
    rw [trace_inv_val]
    apply div_ne_zero (hTtr p.1 hp.1) ((Matrix.isUnit_iff_isUnit_det _).1 p.1.isUnit).ne_zero
  have hVc : ContinuousOn V (T ×ˢ B) := by
    refine ContinuousOn.fun_smul ?_ ?_
    ·
      apply ((htr.comp (hcval.comp continuous_fst)).continuousOn).inv₀ hTtr'
    ·
      apply ((hcval.comp continuous_snd).add ((hdetc.comp (hcval.comp continuous_fst)).smul continuous_const)).continuousOn
  have hWc : ContinuousOn W (T ×ˢ B) := by
    refine ContinuousOn.fun_smul ?_ ?_
    ·
      apply ((htr.comp (hcval.comp (hcinv.comp continuous_fst))).continuousOn).inv₀ hTtr''
    ·
      apply ((hcval.comp (hcinv.comp continuous_snd)).add ((hdetc.comp (hcval.comp (hcinv.comp continuous_fst))).smul continuous_const)).continuousOn
  have hTB : IsCompact (T ×ˢ B) := hT.prod hB
  set M₁ := V '' (T ×ˢ B)
  set M₂ := W '' (T ×ˢ B)
  have hM₁c : IsCompact M₁ := hTB.image_of_continuousOn hVc
  have hM₂c : IsCompact M₂ := hTB.image_of_continuousOn hWc
  set B' : Set (GL (Fin 2) 𝕜) := (Units.embedProduct (Matrix (Fin 2) (Fin 2) 𝕜)) ⁻¹' (M₁ ×ˢ (MulOpposite.op '' M₂))
  have hB'c : IsCompact B' := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hM₁c.prod (hM₂c.image MulOpposite.continuous_op))
  refine ⟨B', hB'c, fun t ht x hx => ?_⟩
  have hx1 : val x⁻¹ * val x = 1 := by
    show (((x⁻¹ : GL (Fin 2) 𝕜)) : Matrix (Fin 2) (Fin 2) 𝕜) * (x : Matrix (Fin 2) (Fin 2) 𝕜) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨(t, x⁻¹ * (t * t) * x), ⟨ht, hx⟩, ?_⟩, ⟨W (t, x⁻¹ * (t * t) * x), ⟨_, ⟨ht, hx⟩, rfl⟩, ?_⟩⟩
  ·
    show V (t, x⁻¹ * (t * t) * x) = ((x⁻¹ * t * x : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜)
    simp only [hV, hval, Units.val_mul]
    apply (conj_eq _ _ _ hx1 (hTtr t ht)).symm
  ·
    show MulOpposite.op (W (t, x⁻¹ * (t * t) * x)) = MulOpposite.op (((x⁻¹ * t * x)⁻¹ : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜)
    congr 1
    have e1 : (x⁻¹ * t * x)⁻¹ = x⁻¹ * t⁻¹ * x := by group
    have e2 : (x⁻¹ * (t * t) * x)⁻¹ = x⁻¹ * (t⁻¹ * t⁻¹) * x := by group
    rw [e1]
    simp only [hW, hval, e2, Units.val_mul]
    apply (conj_eq _ _ _ hx1 (hTtr'' (t, x⁻¹ * (t * t) * x) ⟨ht, hx⟩)).symm


-- created on 2026-10-20
