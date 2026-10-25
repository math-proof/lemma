import Lemma.ModularCurve.X1HeckeOperator
import Lemma.ModularCurve.ShimuraKernel

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve IntermediateField CongruenceSubgroup

open scoped MatrixGroups

section PrivateSupply

variable (L : Type*) [Field L] [Algebra ℚ L]

private theorem laurentBaseChange_mono₃ {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

end PrivateSupply

section Containments

variable {N N' : ℕ}

theorem Gamma1_le_inf_Gamma0_of_mul_dvd {t : ℕ} (h : N * t ∣ N') :
    Gamma1 N' ≤ Gamma1 N ⊓ Gamma0 (N * t) := by
  refine le_inf (Gamma1_le_of_dvd ((dvd_mul_right N t).trans h)) ?_
  intro A hA
  rw [Gamma1_mem] at hA
  rw [Gamma0_mem]
  have := congrArg (ZMod.castHom h (ZMod (N * t))) hA.2.2
  rwa [map_intCast, map_zero] at this

theorem x1x0FunctionFieldC_le_x1FunctionFieldC_of_mul_dvd (K : Type*) [Field K] {t : ℕ}
    (h : N * t ∣ N') : x1x0FunctionFieldC K N (N * t) ≤ x1FunctionFieldC K N' :=
  qExpFunctionFieldC_mono K (Gamma1_le_inf_Gamma0_of_mul_dvd h)

end Containments

section Embeddings

variable (L : Type*) [Field L] [Algebra ℚ L] {N N' : ℕ}

def x1LevelInclBar (h : N ∣ N') :
    laurentBaseChange L (x1FunctionField N) →ₐ[L] laurentBaseChange L (x1FunctionField N') :=
  IntermediateField.inclusion (laurentBaseChange_mono₃ L (x1FunctionFieldC_le_of_dvd ℚ h))

@[simp]
theorem coe_x1LevelInclBar (h : N ∣ N') (x : laurentBaseChange L (x1FunctionField N)) :
    (x1LevelInclBar L h x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

theorem x1LevelInclBar_eq_inclusion (h : N ∣ N')
    (h' : laurentBaseChange L (x1FunctionField N) ≤ laurentBaseChange L (x1FunctionField N')) :
    x1LevelInclBar L h = IntermediateField.inclusion h' :=
  rfl

def x1x0LevelInclBar (t : ℕ) (h : N * t ∣ N') :
    laurentBaseChange L (x1x0FunctionFieldC ℚ N (N * t)) →ₐ[L]
      laurentBaseChange L (x1FunctionField N') :=
  IntermediateField.inclusion
    (laurentBaseChange_mono₃ L (x1x0FunctionFieldC_le_x1FunctionFieldC_of_mul_dvd ℚ h))

@[simp]
theorem coe_x1x0LevelInclBar (t : ℕ) (h : N * t ∣ N')
    (x : laurentBaseChange L (x1x0FunctionFieldC ℚ N (N * t))) :
    (x1x0LevelInclBar L t h x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

theorem x1x0LevelInclBar_eq_inclusion (t : ℕ) (h : N * t ∣ N')
    (h' : laurentBaseChange L (x1x0FunctionFieldC ℚ N (N * t)) ≤
      laurentBaseChange L (x1FunctionField N')) :
    x1x0LevelInclBar L t h = IntermediateField.inclusion h' :=
  rfl

def x1LevelSubstBar (t : ℕ) [NeZero t] (h : N * t ∣ N') :
    laurentBaseChange L (x1FunctionField N) →ₐ[L] laurentBaseChange L (x1FunctionField N') :=
  (x1x0LevelInclBar L t h).comp (heckeBetaOneBar L N t)

theorem x1LevelSubstBar_apply (t : ℕ) [NeZero t] (h : N * t ∣ N')
    (x : laurentBaseChange L (x1FunctionField N)) :
    x1LevelSubstBar L t h x = x1x0LevelInclBar L t h (heckeBetaOneBar L N t x) :=
  rfl

@[simp]
theorem coe_x1LevelSubstBar (t : ℕ) [NeZero t] (h : N * t ∣ N')
    (x : laurentBaseChange L (x1FunctionField N)) :
    (x1LevelSubstBar L t h x : LaurentSeries L) = (heckeBetaOneBar L N t x : LaurentSeries L) := by
  rw [x1LevelSubstBar_apply, coe_x1x0LevelInclBar]

theorem coe_x1LevelSubstBar_of (t : ℕ) [NeZero t] (h : N * t ∣ N') (hβ : HeckeBetaOneDefined N t)
    (x : laurentBaseChange L (x1FunctionField N)) :
    (x1LevelSubstBar L t h x : LaurentSeries L) = qExpand L t (x : LaurentSeries L) := by
  rw [coe_x1LevelSubstBar, coe_heckeBetaOneBar N t hβ]

end Embeddings

namespace JOne

section Total

variable (N N' t : ℕ) [NeZero t]

def DegeneracyPullbackInputs : Prop :=
  ∃ (h : N * t ∣ N') (_ : HeckeBetaOneDefined N t)
    (h₁ : (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)).toRingHom.IsIntegral)
    (h₂ : (x1LevelSubstBar (AlgebraicClosure ℚ) t h).toRingHom.IsIntegral)
    (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) (x1FunctionFieldBar N')),
    FundamentalIdentityAlong (AlgebraicClosure ℚ)
        (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)) h₁ ∧
      FundamentalIdentityAlong (AlgebraicClosure ℚ) (x1LevelSubstBar (AlgebraicClosure ℚ) t h) h₂

open Classical in

def degeneracyPullbackPair : Fin 2 → (JOne N →+ JOne N') :=
  if h : DegeneracyPullbackInputs N N' t then
    haveI := h.snd.snd.snd.snd.fst
    ![Pic0.pullbackAlongHom
        (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h.fst))
        h.snd.snd.fst h.snd.snd.snd.snd.snd.1,
      Pic0.pullbackAlongHom (x1LevelSubstBar (AlgebraicClosure ℚ) t h.fst)
        h.snd.snd.snd.fst h.snd.snd.snd.snd.snd.2]
  else 0

variable {N N' t}

theorem degeneracyPullbackInputs_intro (h : N * t ∣ N') (hβ : HeckeBetaOneDefined N t)
    (h₁ : (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)).toRingHom.IsIntegral)
    (h₂ : (x1LevelSubstBar (AlgebraicClosure ℚ) t h).toRingHom.IsIntegral)
    [hP : HasPrincipalDivisors (AlgebraicClosure ℚ) (x1FunctionFieldBar N')]
    (hFI₁ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)) h₁)
    (hFI₂ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (x1LevelSubstBar (AlgebraicClosure ℚ) t h) h₂) :
    DegeneracyPullbackInputs N N' t :=
  ⟨h, hβ, h₁, h₂, hP, hFI₁, hFI₂⟩

theorem DegeneracyPullbackInputs.mul_dvd (h : DegeneracyPullbackInputs N N' t) : N * t ∣ N' :=
  h.fst

theorem DegeneracyPullbackInputs.betaOneDefined (h : DegeneracyPullbackInputs N N' t) :
    HeckeBetaOneDefined N t :=
  h.snd.fst

theorem degeneracyPullbackPair_eq (h : N * t ∣ N') (hβ : HeckeBetaOneDefined N t)
    (h₁ : (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)).toRingHom.IsIntegral)
    (h₂ : (x1LevelSubstBar (AlgebraicClosure ℚ) t h).toRingHom.IsIntegral)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (x1FunctionFieldBar N')]
    (hFI₁ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)) h₁)
    (hFI₂ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (x1LevelSubstBar (AlgebraicClosure ℚ) t h) h₂) :
    degeneracyPullbackPair N N' t =
      ![Pic0.pullbackAlongHom
          (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)) h₁ hFI₁,
        Pic0.pullbackAlongHom (x1LevelSubstBar (AlgebraicClosure ℚ) t h) h₂ hFI₂] := by
  have hi : DegeneracyPullbackInputs N N' t := degeneracyPullbackInputs_intro h hβ h₁ h₂ hFI₁ hFI₂
  rw [degeneracyPullbackPair, dif_pos hi]

theorem degeneracyPullbackPair_of_not (h : ¬ DegeneracyPullbackInputs N N' t) :
    degeneracyPullbackPair N N' t = 0 := by
  rw [degeneracyPullbackPair, dif_neg h]

theorem degeneracyPullbackPair_apply_of_not (h : ¬ DegeneracyPullbackInputs N N' t) (i : Fin 2)
    (x : JOne N) : degeneracyPullbackPair N N' t i x = 0 := by
  rw [degeneracyPullbackPair_of_not h]
  rfl

end Total

end JOne

end ModularCurve

end
