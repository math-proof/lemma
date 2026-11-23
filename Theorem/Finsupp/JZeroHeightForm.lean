module

public import Theorem.Finsupp.JZeroNaiveHeight
public import Def.AlgebraicCurve_PlaceEvaluation
public import Theorem.Submodule.Repartitions
public import Theorem.Ideal.Mathlib430

public noncomputable section

noncomputable section

open AlgebraicCurve Submodule

namespace AlgebraicCurve

public theorem finiteDimensional_adjoin_range {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range x)) :=
  IntermediateField.finiteDimensional_adjoin fun y _ =>
    ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral


public theorem heightFormAux_two_smul {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (D : Divisor (AlgebraicClosure ℚ) F) :
    heightFormAux s γ b ((2 : ℤ) • D) = 4 * heightFormAux s γ b D := by
  have hsupp : ((2 : ℤ) • D).support = D.support := Finsupp.support_smul_eq two_ne_zero
  simp only [heightFormAux, Finsupp.sum, hsupp, Finsupp.smul_apply, smul_eq_mul, Int.cast_mul,
    Int.cast_ofNat]
  have h1 : ∑ x ∈ D.support, ((2 : ℝ) * (D x : ℝ)) = 2 * ∑ x ∈ D.support, (D x : ℝ) := by
    rw [Finset.mul_sum]
  have h2 : ∑ x ∈ D.support, (2 : ℝ) * (D x : ℝ) * baseHt s b x
      = 2 * ∑ x ∈ D.support, (D x : ℝ) * baseHt s b x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  have h3 : ∑ p ∈ D.support.offDiag, (2 : ℝ) * (D p.1 : ℝ) * ((2 : ℝ) * (D p.2 : ℝ)) * pairHt s p.1 p.2
      = 4 * ∑ p ∈ D.support.offDiag, (D p.1 : ℝ) * (D p.2 : ℝ) * pairHt s p.1 p.2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  have h4 : ∑ x ∈ D.support, (2 : ℝ) * (D x : ℝ) * ((2 : ℝ) * (D x : ℝ) - 1) / 2 * baseHt s b x
      = 4 * (∑ x ∈ D.support, (D x : ℝ) * ((D x : ℝ) - 1) / 2 * baseHt s b x)
        + ∑ x ∈ D.support, (D x : ℝ) * baseHt s b x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h1, h2, h3, h4]
  ring


public theorem heightForm_two_smul {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (D : Divisor (AlgebraicClosure ℚ) F) :
    heightForm s γ b ((2 : ℤ) • D) = 4 * heightForm s γ b D := by
  unfold heightForm
  rw [two_zsmul, Finsupp.erase_add, ← two_zsmul]
  exact heightFormAux_two_smul s γ b _


public theorem heightForm_add_single_base {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (D : Divisor (AlgebraicClosure ℚ) F) (m : ℤ) :
    heightForm s γ b (D + Finsupp.single b m) = heightForm s γ b D := by
  unfold heightForm
  rw [Finsupp.erase_add, Finsupp.erase_single, add_zero]

end AlgebraicCurve

namespace ModularCurve

variable (N : ℕ) [NeZero N]


public theorem JZero.heightForm_two_smul {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    JZero.heightForm N s ((2 : ℤ) • D) = 4 * JZero.heightForm N s D :=
  AlgebraicCurve.heightForm_two_smul s _ _ D


public theorem JZero.heightForm_add_single_cuspInftyBar {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (m : ℤ) :
    JZero.heightForm N s (D + Finsupp.single (cuspInftyBar N) m) = JZero.heightForm N s D :=
  AlgebraicCurve.heightForm_add_single_base s _ _ D m

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]


public theorem JZero.mem_repHeights_iff (n : ℕ) (c : ↥(JZero N ^+ ↥K.fixingSubgroup)) (x : ℝ) :
    x ∈ JZero.repHeights N K n c ↔ ∃ D, JZero.IsRepOf N K n c D ∧ x = divNaiveHeight N K n D := by
  constructor
  · rintro ⟨D, E, h1, h2, h3, h4, h5⟩
    exact ⟨D, ⟨E, h1, h2, h3, h4⟩, h5⟩
  · rintro ⟨D, ⟨E, h1, h2, h3, h4⟩, h5⟩
    exact ⟨D, E, h1, h2, h3, h4, h5⟩

variable {N K}

omit [FiniteDimensional ℚ K] in


public theorem JZero.IsRepOf.nsmul {n : ℕ} {c : ↥(JZero N ^+ ↥K.fixingSubgroup)}
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (h : JZero.IsRepOf N K n c D)
    (m : ℕ) : JZero.IsRepOf N K (m * n) (m • c) (m • D) := by
  obtain ⟨E, hD, hshape, hstab, hc⟩ := h
  refine ⟨m • E, fun v => ?_, ?_, fun σ hσ => ?_, ?_⟩
  · rw [Finsupp.smul_apply]
    exact nsmul_nonneg (hD v) m
  · rw [← hshape, smul_add, AddSubmonoidClass.coe_nsmul, Nat.cast_mul, mul_smul, natCast_zsmul]
  · have key := map_nsmul (DistribSMul.toAddMonoidHom
      (Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      (arithmeticGalois (modularFunctionFieldFull N) σ)) m D
    simp only [DistribSMul.toAddMonoidHom_apply] at key
    rw [key, hstab σ hσ]
  · have key : Pic0.mk (m • E) = m • Pic0.mk E := QuotientAddGroup.mk_nsmul _ E m
    rw [key, hc, AddSubmonoidClass.coe_nsmul]

omit [FiniteDimensional ℚ K] in


public theorem JZero.IsRepOf.add_single {n : ℕ} {c : ↥(JZero N ^+ ↥K.fixingSubgroup)}
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (h : JZero.IsRepOf N K n c D)
    (p : ℕ)
    (hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
      arithmeticGalois (modularFunctionFieldFull N) σ • cuspInftyBar N = cuspInftyBar N) :
    JZero.IsRepOf N K (n + p) c (D + (p : ℤ) • Finsupp.single (cuspInftyBar N) 1) := by
  obtain ⟨E, hD, hshape, hstab, hc⟩ := h
  refine ⟨E, fun v => ?_, ?_, fun σ hσ => ?_, hc⟩
  · classical
    have h0 : (0 : ℤ) ≤ ((p : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) v := by
      rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs <;> simp
    rw [Finsupp.add_apply]
    exact add_nonneg (hD v) h0
  · rw [← hshape, Nat.cast_add, add_smul, add_assoc]
  · have key := map_zsmul (DistribSMul.toAddMonoidHom
      (Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      (arithmeticGalois (modularFunctionFieldFull N) σ)) (p : ℤ)
      (Finsupp.single (cuspInftyBar N) (1 : ℤ))
    simp only [DistribSMul.toAddMonoidHom_apply] at key
    rw [smul_add, hstab σ hσ, key, AlgebraicCurve.SemilinearAut.smul_single, hfix σ hσ]

end ModularCurve

end
