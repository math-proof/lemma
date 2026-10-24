import Mathlib
import Lemma.Definitions.Def_ModularForm_HeckeOperator
import Lemma.Definitions.Def_ModularForm_AtkinLehnerDatum

set_option autoImplicit false
noncomputable section
open Matrix UpperHalfPlane CongruenceSubgroup ModularForm OnePoint
open scoped MatrixGroups ModularForm Manifold

namespace FreyPackage.ModMCarrier

section Cocycle
variable {R M d : ℕ}

def diagMatInt (d : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(d : ℤ), 0; 0, 1]

lemma exists_cocycle_rescale (hdRM : d * R ∣ M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 R ∧
      diagMatInt d * (γ : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) * diagMatInt d := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hMc : (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hγ; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set e : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with he
  have hγmat : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, e] := by
    rw [ha, hb, hc, he]; exact Matrix.eta_fin_two _
  have hdRMc : ((d * R : ℕ) : ℤ) ∣ c := dvd_trans (by exact_mod_cast hdRM) hMc
  obtain ⟨c', hc'⟩ := hdRMc
  rw [Nat.cast_mul] at hc'
  have hdetδ : Matrix.det !![a, (d : ℤ) * b; (R : ℤ) * c', e] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + b * hc'
  refine ⟨⟨_, hdetδ⟩, ?_, ?_⟩
  · rw [Gamma0_mem]
    show (((R : ℤ) * c' : ℤ) : ZMod R) = 0
    push_cast; rw [ZMod.natCast_self, zero_mul]
  · show diagMatInt d * (γ : Matrix (Fin 2) (Fin 2) ℤ)
      = !![a, (d : ℤ) * b; (R : ℤ) * c', e] * diagMatInt d
    rw [hγmat]; unfold diagMatInt
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show ((d : ℤ) * a + 0 * c : ℤ) = a * (d : ℤ) + (d : ℤ) * b * 0; ring
    · show ((d : ℤ) * b + 0 * e : ℤ) = a * 0 + (d : ℤ) * b * 1; ring
    · show (0 * a + 1 * c : ℤ) = (R : ℤ) * c' * (d : ℤ) + e * 0; linear_combination hc'
    · show (0 * b + 1 * e : ℤ) = (R : ℤ) * c' * 0 + e * 1; ring

private lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

private lemma map_int_mul_eq (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * B).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * B.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

lemma diagMatInt_map_eq (hd : d ≠ 0) :
    (diagMatInt d).map (algebraMap ℤ ℝ)
      = ((heckeDiagMatrix d : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [val_heckeDiagMatrix hd]; unfold diagMatInt
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma rescaleSlash_slash [NeZero M] (hdRM : d * R ∣ M) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (f ∣[k] heckeDiagMatrix d) ∣[k] γ = f ∣[k] heckeDiagMatrix d := by
  have hd : d ≠ 0 := by
    rintro rfl; exact NeZero.ne M (Nat.eq_zero_of_zero_dvd ((zero_mul R ▸ hdRM)))
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  obtain ⟨δ, hδ, hconj⟩ := exists_cocycle_rescale hdRM hg
  have hGL : heckeDiagMatrix d * Matrix.SpecialLinearGroup.mapGL ℝ g
      = Matrix.SpecialLinearGroup.mapGL ℝ δ * heckeDiagMatrix d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (heckeDiagMatrix d : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ((Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        (heckeDiagMatrix d : Matrix (Fin 2) (Fin 2) ℝ)
    rw [← diagMatInt_map_eq hd, mapGL_coe_eq, mapGL_coe_eq, ← map_int_mul_eq, ← map_int_mul_eq,
      hconj]
  calc (f ∣[k] heckeDiagMatrix d) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ g
      = f ∣[k] (heckeDiagMatrix d * Matrix.SpecialLinearGroup.mapGL ℝ g) :=
        (SlashAction.slash_mul k _ _ f).symm
    _ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ δ * heckeDiagMatrix d) := by rw [hGL]
    _ = (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ δ) ∣[k] heckeDiagMatrix d :=
        SlashAction.slash_mul k _ _ f
    _ = f ∣[k] heckeDiagMatrix d := by
        rw [hf (Matrix.SpecialLinearGroup.mapGL ℝ δ) (Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩)]

end Cocycle

section Cusps
variable {R M d : ℕ}

def heckeDiagMatrixQ (hd : d ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(d : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp; exact_mod_cast hd)

lemma heckeDiagMatrixQ_map (hd : d ≠ 0) :
    (heckeDiagMatrixQ hd).map (Rat.castHom ℝ) = heckeDiagMatrix d := by
  apply Units.ext
  rw [val_heckeDiagMatrix hd]
  show (heckeDiagMatrixQ hd : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) = _
  unfold heckeDiagMatrixQ
  ext i j; fin_cases i <;> fin_cases j <;> simp

private lemma isCusp_smul_of_rat {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) {g : GL (Fin 2) ℝ}
    (gQ : GL (Fin 2) ℚ) (hg : gQ.map (Rat.castHom ℝ) = g) : IsCusp (g • c) 𝒮ℒ := by
  subst hg
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  exact ⟨gQ • c₀, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

lemma rescaleSlash_isZeroAt [NeZero M] [NeZero R] (hd : d ≠ 0) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsZeroAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsZeroAt c (f ∣[k] heckeDiagMatrix d) k := by
  refine IsZeroAt.smul_iff.mp (hf _ ?_)
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact isCusp_smul_of_rat hc (heckeDiagMatrixQ hd) (heckeDiagMatrixQ_map hd)

end Cusps

section Rescale
variable {R M d : ℕ} [NeZero M]

private lemma aux_neZero_d (hdRM : d * R ∣ M) : d ≠ 0 := by
  rintro rfl; exact NeZero.ne M (Nat.eq_zero_of_zero_dvd (zero_mul R ▸ hdRM))

private lemma aux_neZero_R (hdRM : d * R ∣ M) : NeZero R :=
  ⟨by rintro rfl; exact NeZero.ne M (Nat.eq_zero_of_zero_dvd (mul_zero d ▸ hdRM))⟩

def rescaleLin (hdRM : d * R ∣ M) (k : ℤ) :
    CuspForm (Gamma0 R) k →ₗ[ℂ] CuspForm (Gamma0 M) k where
  toFun f :=
    haveI : NeZero R := aux_neZero_R hdRM
    { toFun := ⇑f ∣[k] heckeDiagMatrix d
      slash_action_eq' := fun γ hγ => rescaleSlash_slash hdRM k
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) hγ
      holo' := (CuspFormClass.holo f).slash k (heckeDiagMatrix d)
      zero_at_cusps' := fun {c} hc => rescaleSlash_isZeroAt (aux_neZero_d hdRM) k
        (fun c' hc' => CuspFormClass.zero_at_cusps f hc') hc }
  map_add' f g := DFunLike.coe_injective <| by
    show (⇑(f + g)) ∣[k] heckeDiagMatrix d
      = (⇑f ∣[k] heckeDiagMatrix d) + (⇑g ∣[k] heckeDiagMatrix d)
    rw [CuspForm.coe_add, SlashAction.add_slash]
  map_smul' c f := DFunLike.coe_injective <| by
    show (⇑(c • f)) ∣[k] heckeDiagMatrix d = c • (⇑f ∣[k] heckeDiagMatrix d)
    rw [CuspForm.IsGLPos.coe_smul]
    simp only [ModularForm.smul_slash, σ_heckeDiagMatrix, ContinuousAlgEquiv.refl_apply]

@[simp] lemma coe_rescaleLin_apply (hdRM : d * R ∣ M) (k : ℤ) (f : CuspForm (Gamma0 R) k) :
    ⇑(rescaleLin hdRM k f) = ⇑f ∣[k] heckeDiagMatrix d := rfl

end Rescale

section AtkinLehnerSpecialization
variable {M q' : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q')

lemma _root_.ModularForm.AtkinLehnerDatum.q_mul_R_dvd : q' * W.R ∣ M :=
  ⟨1, W.hM.trans (mul_one (q' * W.R)).symm⟩

abbrev rescaleLinAL (k : ℤ) :
    CuspForm (Gamma0 W.R) k →ₗ[ℂ] CuspForm (Gamma0 M) k :=
  rescaleLin W.q_mul_R_dvd k

end AtkinLehnerSpecialization

end FreyPackage.ModMCarrier
