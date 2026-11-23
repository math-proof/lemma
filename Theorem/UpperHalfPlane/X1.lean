module

public import Mathlib
public import Theorem.LaurentSeries.ArithmeticGalois

public noncomputable section

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

section Restrict

variable {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}


@[simp]
public theorem coe_restrictForm (h : Γ' ≤ Γ) (f : ModularForm Γ k) :
    (⇑(restrictForm h f) : ℍ → ℂ) = f :=
  rfl


public theorem restrictForm_apply (h : Γ' ≤ Γ) (f : ModularForm Γ k) (τ : ℍ) :
    restrictForm h f τ = f τ :=
  rfl

end Restrict

section Integral


public theorem IsIntegralQExp.coeff {f : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp f p) (n : ℕ) :
    ((PowerSeries.coeff n p : ℤ) : ℂ) = PowerSeries.coeff n (qExpansion 1 f) := by
  rw [← h, PowerSeries.coeff_map, eq_intCast]


public theorem isIntegralQExp_iff {f : ℍ → ℂ} {p : PowerSeries ℤ} :
    IsIntegralQExp f p ↔ ∀ n : ℕ, ((PowerSeries.coeff n p : ℤ) : ℂ) = PowerSeries.coeff n (qExpansion 1 f) := by
  refine ⟨fun h n => h.coeff n, fun h => ?_⟩
  ext n
  rw [PowerSeries.coeff_map, eq_intCast]
  exact h n


public theorem IsIntegralQExp.unique {f : ℍ → ℂ} {p p' : PowerSeries ℤ} (h : IsIntegralQExp f p)
    (h' : IsIntegralQExp f p') : p = p' := by
  ext n
  have := (h.coeff n).trans (h'.coeff n).symm
  exact_mod_cast this


public theorem isIntegralQExp_one : IsIntegralQExp (1 : ℍ → ℂ) 1 := by
  rw [IsIntegralQExp, map_one, qExpansion_one]


public theorem isIntegralQExp_zero : IsIntegralQExp (0 : ℍ → ℂ) 0 := by
  rw [IsIntegralQExp, map_zero, qExpansion_zero]

end Integral

section FunctionField

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ))


@[simp]
public theorem intSeriesC_one : intSeriesC K 1 = 1 := by
  simp [intSeriesC]


@[simp]
public theorem intSeriesC_zero : intSeriesC K 0 = 0 := by
  simp [intSeriesC]


public theorem intSeriesC_mul (p p' : PowerSeries ℤ) : intSeriesC K (p * p') = intSeriesC K p * intSeriesC K p' := by
  simp [intSeriesC]


public theorem mem_intFormRatiosC {k : ℤ} (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC K pg ≠ 0) :
    intSeriesC K pf / intSeriesC K pg ∈ intFormRatiosC K Γ :=
  ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩


public theorem one_mem_intFormRatiosC : (1 : LaurentSeries K) ∈ intFormRatiosC K Γ := by
  refine ⟨0, 1, 1, 1, 1, ?_, ?_, by simp, by simp⟩ <;>
  · show IsIntegralQExp (⇑(1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0)) 1
    rw [ModularForm.one_coe_eq_one]
    exact isIntegralQExp_one


public theorem intFormRatiosC_subset : intFormRatiosC K Γ ⊆ (qExpFunctionFieldC K Γ : Set (LaurentSeries K)) :=
  IntermediateField.subset_adjoin K _

variable {K Γ} in

public theorem div_mem_qExpFunctionFieldC {k : ℤ} (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC K pg ≠ 0) :
    intSeriesC K pf / intSeriesC K pg ∈ qExpFunctionFieldC K Γ :=
  intFormRatiosC_subset K Γ (mem_intFormRatiosC f g hf hg hg0)

variable {Γ} in


public theorem intFormRatiosC_mono {Γ' : Subgroup SL(2, ℤ)} (h : Γ' ≤ Γ) :
    intFormRatiosC K Γ ⊆ intFormRatiosC K Γ' := by
  rintro x ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  have h' : (Γ' : Subgroup (GL (Fin 2) ℝ)) ≤ (Γ : Subgroup (GL (Fin 2) ℝ)) := Subgroup.map_mono h
  exact ⟨k, restrictForm h' f, restrictForm h' g, pf, pg, hf, hg, hg0, rfl⟩

variable {Γ} in


public theorem qExpFunctionFieldC_mono {Γ' : Subgroup SL(2, ℤ)} (h : Γ' ≤ Γ) :
    qExpFunctionFieldC K Γ ≤ qExpFunctionFieldC K Γ' :=
  IntermediateField.adjoin.mono K _ _ (intFormRatiosC_mono K h)

end FunctionField

section LevelOne

variable (K : Type*) [Field K] (M : ℕ)


public theorem x1FunctionFieldC_rat : x1FunctionFieldC ℚ M = x1FunctionField M := rfl


public theorem x1FunctionFieldC_le_x1x0 (t : ℕ) : x1FunctionFieldC K M ≤ x1x0FunctionFieldC K M t :=
  qExpFunctionFieldC_mono K inf_le_left


public theorem x1x0FunctionFieldC_one : x1x0FunctionFieldC K M 1 = x1FunctionFieldC K M := by
  have : Gamma1 M ⊓ Gamma0 1 = Gamma1 M := by
    refine le_antisymm inf_le_left (le_inf le_rfl ?_)
    intro A _
    rw [Gamma0_mem]
    exact Subsingleton.elim _ _
  rw [x1x0FunctionFieldC, this, x1FunctionFieldC]

variable {M} in


public theorem Gamma1_le_of_dvd {M' : ℕ} (h : M ∣ M') : Gamma1 M' ≤ Gamma1 M := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  obtain ⟨h00, h11, h10⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ZMod.castHom h (ZMod M)) h00
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod M)) h11
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod M)) h10
    rwa [map_intCast, map_zero] at this

variable {M} in


public theorem x1FunctionFieldC_le_of_dvd {M' : ℕ} (h : M ∣ M') :
    x1FunctionFieldC K M ≤ x1FunctionFieldC K M' :=
  qExpFunctionFieldC_mono K (Gamma1_le_of_dvd h)

end LevelOne

section Jacobian

variable (M : ℕ)


@[simp]
public theorem JOne.torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : Pic0.torsion (AlgebraicClosure ℚ) (x1FunctionFieldBar M) n) :
    JOne.torsionGaloisRep M n σ x = arithmeticGalois (x1FunctionField M) σ • x :=
  rfl


public theorem JOne.coe_torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : Pic0.torsion (AlgebraicClosure ℚ) (x1FunctionFieldBar M) n) :
    ((JOne.torsionGaloisRep M n σ x : Pic0.torsion (AlgebraicClosure ℚ) (x1FunctionFieldBar M) n) :
        JOne M) = σ • (x : JOne M) :=
  rfl

