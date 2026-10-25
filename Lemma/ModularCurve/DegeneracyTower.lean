import Lemma.ModularCurve.HeckeOperator

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section PrivateSupply

variable (L : Type*) [Field L] [Algebra ℚ L]

private theorem laurentBaseChange_mono'' {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

end PrivateSupply

section TowerMaps

variable (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N] [NeZero M]

def towerInclBar (h : N ∣ M) :
    laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull M) :=
  IntermediateField.inclusion (laurentBaseChange_mono'' L (full_degeneracy_le h))

@[simp]
theorem coe_towerInclBar (h : N ∣ M) (x : laurentBaseChange L (modularFunctionFieldFull N)) :
    (towerInclBar L h x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

theorem towerInclBar_eq_inclusion (h : N ∣ M)
    (h' : laurentBaseChange L (modularFunctionFieldFull N) ≤
      laurentBaseChange L (modularFunctionFieldFull M)) :
    towerInclBar L h = IntermediateField.inclusion h' :=
  rfl

theorem towerInclBar_comp_towerInclBar {M' : ℕ} [NeZero M'] (h₁ : N ∣ M') (h₂ : M' ∣ M)
    (h : N ∣ M) : (towerInclBar L h₂).comp (towerInclBar L h₁) = towerInclBar L h := by
  refine AlgHom.ext fun x => Subtype.ext ?_
  rw [AlgHom.comp_apply, coe_towerInclBar, coe_towerInclBar, coe_towerInclBar]

theorem towerInclBar_self (h : N ∣ N) (x : laurentBaseChange L (modularFunctionFieldFull N)) :
    towerInclBar L h x = x :=
  Subtype.ext (coe_towerInclBar L h x)

variable (N) in

def towerSubstBar (ℓ : ℕ) [NeZero ℓ] (h : N * ℓ ∣ M) :
    laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull M) :=
  (towerInclBar L h).comp (heckeBetaBar L N ℓ)

@[simp]
theorem coe_towerSubstBar (ℓ : ℕ) [NeZero ℓ] (h : N * ℓ ∣ M)
    (x : laurentBaseChange L (modularFunctionFieldFull N)) :
    (towerSubstBar L N ℓ h x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

theorem towerSubstBar_congr {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ = ℓ') (h : N * ℓ ∣ M)
    (h' : N * ℓ' ∣ M) : towerSubstBar L N ℓ h = towerSubstBar L N ℓ' h' := by
  subst hℓ
  rfl

end TowerMaps

section Composites

variable (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N] [NeZero M] (ℓ ℓ' : ℕ)
  [NeZero ℓ] [NeZero ℓ']

theorem heckeAlphaBar_eq_towerInclBar : heckeAlphaBar L N ℓ = towerInclBar L (dvd_mul_right N ℓ) :=
  rfl

theorem heckeBetaBar_eq_towerSubstBar : heckeBetaBar L N ℓ = towerSubstBar L N ℓ dvd_rfl := by
  refine AlgHom.ext fun x => Subtype.ext ?_
  rw [coe_towerSubstBar, coe_heckeBetaBar]

theorem towerInclBar_comp_heckeAlphaBar (h : N * ℓ ∣ M) (h' : N ∣ M) :
    (towerInclBar L h).comp (heckeAlphaBar L N ℓ) = towerInclBar L h' := by
  refine AlgHom.ext fun x => Subtype.ext ?_
  rw [AlgHom.comp_apply, coe_towerInclBar, coe_heckeAlphaBar, coe_towerInclBar]

theorem towerInclBar_comp_heckeBetaBar (h : N * ℓ ∣ M) :
    (towerInclBar L h).comp (heckeBetaBar L N ℓ) = towerSubstBar L N ℓ h :=
  rfl

theorem towerSubstBar_comp_heckeAlphaBar (h : N * ℓ' * ℓ ∣ M) (h' : N * ℓ ∣ M) :
    (towerSubstBar L (N * ℓ') ℓ h).comp (heckeAlphaBar L N ℓ') = towerSubstBar L N ℓ h' := by
  refine AlgHom.ext fun x => Subtype.ext ?_
  rw [AlgHom.comp_apply, coe_towerSubstBar, coe_heckeAlphaBar, coe_towerSubstBar]

theorem towerSubstBar_comp_heckeBetaBar (h : N * ℓ' * ℓ ∣ M) (h' : N * (ℓ * ℓ') ∣ M) :
    (towerSubstBar L (N * ℓ') ℓ h).comp (heckeBetaBar L N ℓ') = towerSubstBar L N (ℓ * ℓ') h' := by
  refine AlgHom.ext fun x => Subtype.ext ?_
  rw [AlgHom.comp_apply, coe_towerSubstBar, coe_heckeBetaBar, coe_towerSubstBar]
  exact qExpand_qExpand ℓ' ℓ _

theorem heckeSquareBar_commutes (h₁ : N * ℓ ∣ M) (h₂ : N * ℓ' * ℓ ∣ M) :
    (towerInclBar L h₁).comp (heckeBetaBar L N ℓ) =
      (towerSubstBar L (N * ℓ') ℓ h₂).comp (heckeAlphaBar L N ℓ') := by
  rw [towerInclBar_comp_heckeBetaBar, towerSubstBar_comp_heckeAlphaBar]

end Composites

section Exchange

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ ℓ' M : ℕ) [NeZero N] [NeZero ℓ] [NeZero ℓ']
  [NeZero M]

omit [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M] in

theorem dvd_of_eq_roof (hM : M = N * ℓ * ℓ') : N * ℓ ∣ M ∧ N * ℓ' * ℓ ∣ M :=
  ⟨⟨ℓ', hM⟩, ⟨1, by rw [hM]; ring⟩⟩

def HeckeExchangeAt (hM : M = N * ℓ * ℓ') : Prop :=
  ∀ [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull M))]
    (hβ : (heckeBetaBar L N ℓ).toRingHom.IsIntegral)
    (hα' : (heckeAlphaBar L N ℓ').toRingHom.IsIntegral)
    (hu : (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1).toRingHom.IsIntegral)
    (hu' : (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).toRingHom.IsIntegral)
    (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ')))),
    Divisor.pullbackAlong (heckeBetaBar L N ℓ) hβ
        (Divisor.pushforwardAlong (heckeAlphaBar L N ℓ') hα' D)
      = Divisor.pushforwardAlong (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1) hu
          (Divisor.pullbackAlong (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2) hu' D)

end Exchange

end ModularCurve

end
