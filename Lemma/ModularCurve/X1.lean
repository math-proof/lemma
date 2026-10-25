import Mathlib
import Lemma.ModularCurve.ArithmeticGalois

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

section Restrict

variable {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

def restrictForm (h : Γ' ≤ Γ) (f : ModularForm Γ k) : ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[simp]
theorem coe_restrictForm (h : Γ' ≤ Γ) (f : ModularForm Γ k) :
    (⇑(restrictForm h f) : ℍ → ℂ) = f :=
  rfl

theorem restrictForm_apply (h : Γ' ≤ Γ) (f : ModularForm Γ k) (τ : ℍ) :
    restrictForm h f τ = f τ :=
  rfl

end Restrict

section Integral

def IsIntegralQExp (f : ℍ → ℂ) (p : PowerSeries ℤ) : Prop :=
  p.map (Int.castRingHom ℂ) = qExpansion 1 f

theorem IsIntegralQExp.coeff {f : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp f p) (n : ℕ) :
    ((PowerSeries.coeff n p : ℤ) : ℂ) = PowerSeries.coeff n (qExpansion 1 f) := by
  rw [← h, PowerSeries.coeff_map, eq_intCast]

theorem isIntegralQExp_iff {f : ℍ → ℂ} {p : PowerSeries ℤ} :
    IsIntegralQExp f p ↔ ∀ n : ℕ, ((PowerSeries.coeff n p : ℤ) : ℂ) = PowerSeries.coeff n (qExpansion 1 f) := by
  refine ⟨fun h n => h.coeff n, fun h => ?_⟩
  ext n
  rw [PowerSeries.coeff_map, eq_intCast]
  exact h n

theorem IsIntegralQExp.unique {f : ℍ → ℂ} {p p' : PowerSeries ℤ} (h : IsIntegralQExp f p)
    (h' : IsIntegralQExp f p') : p = p' := by
  ext n
  have := (h.coeff n).trans (h'.coeff n).symm
  exact_mod_cast this

theorem isIntegralQExp_one : IsIntegralQExp (1 : ℍ → ℂ) 1 := by
  rw [IsIntegralQExp, map_one, qExpansion_one]

theorem isIntegralQExp_zero : IsIntegralQExp (0 : ℍ → ℂ) 0 := by
  rw [IsIntegralQExp, map_zero, qExpansion_zero]

end Integral

section FunctionField

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ))

def intSeriesC (p : PowerSeries ℤ) : LaurentSeries K :=
  HahnSeries.ofPowerSeries ℤ K (p.map (Int.castRingHom K))

@[simp]
theorem intSeriesC_one : intSeriesC K 1 = 1 := by
  simp [intSeriesC]

@[simp]
theorem intSeriesC_zero : intSeriesC K 0 = 0 := by
  simp [intSeriesC]

theorem intSeriesC_mul (p p' : PowerSeries ℤ) : intSeriesC K (p * p') = intSeriesC K p * intSeriesC K p' := by
  simp [intSeriesC]

def intFormRatiosC : Set (LaurentSeries K) :=
  {x | ∃ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ),
      IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ intSeriesC K pg ≠ 0 ∧
        x = intSeriesC K pf / intSeriesC K pg}

variable {K Γ} in
theorem mem_intFormRatiosC {k : ℤ} (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC K pg ≠ 0) :
    intSeriesC K pf / intSeriesC K pg ∈ intFormRatiosC K Γ :=
  ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩

theorem one_mem_intFormRatiosC : (1 : LaurentSeries K) ∈ intFormRatiosC K Γ := by
  refine ⟨0, 1, 1, 1, 1, ?_, ?_, by simp, by simp⟩ <;>
  · show IsIntegralQExp (⇑(1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0)) 1
    rw [ModularForm.one_coe_eq_one]
    exact isIntegralQExp_one

def qExpFunctionFieldC : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K (intFormRatiosC K Γ)

theorem intFormRatiosC_subset : intFormRatiosC K Γ ⊆ (qExpFunctionFieldC K Γ : Set (LaurentSeries K)) :=
  IntermediateField.subset_adjoin K _

variable {K Γ} in
theorem div_mem_qExpFunctionFieldC {k : ℤ} (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC K pg ≠ 0) :
    intSeriesC K pf / intSeriesC K pg ∈ qExpFunctionFieldC K Γ :=
  intFormRatiosC_subset K Γ (mem_intFormRatiosC f g hf hg hg0)

variable {Γ} in

theorem intFormRatiosC_mono {Γ' : Subgroup SL(2, ℤ)} (h : Γ' ≤ Γ) :
    intFormRatiosC K Γ ⊆ intFormRatiosC K Γ' := by
  rintro x ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  have h' : (Γ' : Subgroup (GL (Fin 2) ℝ)) ≤ (Γ : Subgroup (GL (Fin 2) ℝ)) := Subgroup.map_mono h
  exact ⟨k, restrictForm h' f, restrictForm h' g, pf, pg, hf, hg, hg0, rfl⟩

variable {Γ} in

theorem qExpFunctionFieldC_mono {Γ' : Subgroup SL(2, ℤ)} (h : Γ' ≤ Γ) :
    qExpFunctionFieldC K Γ ≤ qExpFunctionFieldC K Γ' :=
  IntermediateField.adjoin.mono K _ _ (intFormRatiosC_mono K h)

end FunctionField

section LevelOne

variable (K : Type*) [Field K] (M : ℕ)

def x1FunctionFieldC : IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (Gamma1 M)

abbrev x1FunctionField : IntermediateField ℚ (LaurentSeries ℚ) :=
  x1FunctionFieldC ℚ M

theorem x1FunctionFieldC_rat : x1FunctionFieldC ℚ M = x1FunctionField M := rfl

def x1x0FunctionFieldC (t : ℕ) : IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (Gamma1 M ⊓ Gamma0 t)

theorem x1FunctionFieldC_le_x1x0 (t : ℕ) : x1FunctionFieldC K M ≤ x1x0FunctionFieldC K M t :=
  qExpFunctionFieldC_mono K inf_le_left

theorem x1x0FunctionFieldC_one : x1x0FunctionFieldC K M 1 = x1FunctionFieldC K M := by
  have : Gamma1 M ⊓ Gamma0 1 = Gamma1 M := by
    refine le_antisymm inf_le_left (le_inf le_rfl ?_)
    intro A _
    rw [Gamma0_mem]
    exact Subsingleton.elim _ _
  rw [x1x0FunctionFieldC, this, x1FunctionFieldC]

variable {M} in

theorem Gamma1_le_of_dvd {M' : ℕ} (h : M ∣ M') : Gamma1 M' ≤ Gamma1 M := by
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

theorem x1FunctionFieldC_le_of_dvd {M' : ℕ} (h : M ∣ M') :
    x1FunctionFieldC K M ≤ x1FunctionFieldC K M' :=
  qExpFunctionFieldC_mono K (Gamma1_le_of_dvd h)

end LevelOne

section Jacobian

variable (M : ℕ)

abbrev x1FunctionFieldBar :
    IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField M)

abbrev JOne : Type _ :=
  Pic0 (AlgebraicClosure ℚ) (x1FunctionFieldBar M)

example : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JOne M) :=
  inferInstance

def JOne.torsionGaloisRep (n : ℕ) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End (ZMod n) (Pic0.torsion (AlgebraicClosure ℚ) (x1FunctionFieldBar M) n) :=
  (SemilinearAut.torsionRep _ _ n).comp (arithmeticGalois (x1FunctionField M))

@[simp]
theorem JOne.torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : Pic0.torsion (AlgebraicClosure ℚ) (x1FunctionFieldBar M) n) :
    JOne.torsionGaloisRep M n σ x = arithmeticGalois (x1FunctionField M) σ • x :=
  rfl

theorem JOne.coe_torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : Pic0.torsion (AlgebraicClosure ℚ) (x1FunctionFieldBar M) n) :
    ((JOne.torsionGaloisRep M n σ x : Pic0.torsion (AlgebraicClosure ℚ) (x1FunctionFieldBar M) n) :
        JOne M) = σ • (x : JOne M) :=
  rfl

abbrev JOneC (K : Type*) [Field K] : Type _ :=
  Pic0 K (x1FunctionFieldC K M)

example (K : Type*) [Field K] : AddCommGroup (JOneC M K) := inferInstance

end Jacobian

end ModularCurve

end
