import Lemma.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

open IsDedekindDomain NumberField MeasureTheory Matrix
open AutomorphicForm FLT.SmoothVectors

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => chiDet (𝓞 F) F η g * φ g

@[simp] theorem fnTwist_apply (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    fnTwist F η φ g = chiDet (𝓞 F) F η g * φ g := rfl

@[simp] theorem fnTwist_zero (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :
    fnTwist F η (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  ext g; simp [fnTwist]

theorem fnTwist_one (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    fnTwist F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) φ = φ := by
  ext g; simp [fnTwist, chiDet]

theorem fnTwist_fnTwist (η₁ η₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    fnTwist F η₁ (fnTwist F η₂ φ) = fnTwist F (η₁ * η₂) φ := by
  ext g; simp only [fnTwist, chiDet, MonoidHom.mul_apply, Units.val_mul]; ring

theorem det_centralScalar (z : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z ^ 2 := by
  rw [show centralScalar (𝓞 F) F = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem chiDet_centralScalar_mul (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    chiDet (𝓞 F) F η (centralScalar (𝓞 F) F z * g) =
      ((η z : ℂˣ) : ℂ) ^ 2 * chiDet (𝓞 F) F η g := by
  simp only [chiDet, map_mul, det_centralScalar F, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]

def twistedCentralChar (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : Z →* ℂˣ :=
  ξ * (η.comp Z.subtype) ^ 2

theorem chiDet_globalPoints_mul (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hηF : IsIdeleClassChar (𝓞 F) F η) (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    chiDet (𝓞 F) F η (globalPoints (𝓞 F) F γ * g) = chiDet (𝓞 F) F η g := by
  unfold chiDet
  congr 1
  rw [map_mul, globalPoints, Matrix.GeneralLinearGroup.map_det, map_mul,
    hηF (Matrix.GeneralLinearGroup.det γ), one_mul]

theorem isLsXiFunction_fnTwist {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hηF : IsIdeleClassChar (𝓞 F) F η)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) :
    IsLsXiFunction (𝓞 F) F Z (twistedCentralChar F Z ξ η) (fnTwist F η φ) := by
  refine ⟨fun γ g => ?_, fun z g => ?_⟩
  · simp only [fnTwist_apply, chiDet_globalPoints_mul F η hηF, hφ.left_invariant γ g]
  · simp only [fnTwist_apply, chiDet_centralScalar_mul F, hφ.central_transform z g,
      twistedCentralChar, MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]
    ring

theorem isSmoothVector_rightTranslationFn_mul {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {M : Type*} [Mul M] {H : Subgroup G} {φ ψ : G → M}
    (hφ : IsSmoothVector H (RightTranslationFn.mk (G := G) φ))
    (hψ : IsSmoothVector H (RightTranslationFn.mk (G := G) ψ)) :
    IsSmoothVector H (RightTranslationFn.mk (G := G) (fun g => φ g * ψ g)) := by
  rw [isSmoothVector_iff_isOpen_stabilizer]
  refine Subgroup.isOpen_mono ?_ (isOpen_coe_inf_stabilizer hφ hψ)
  intro k hk
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    Subgroup.smul_def, Subgroup.smul_def] at hk
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  refine RightTranslationFn.ext fun g => ?_
  have hφk : φ (g * ↑k) = φ g := by
    have := congrFun (congrArg RightTranslationFn.toFun hk.1) g
    simp only [RightTranslationFn.toFun_smul] at this
    exact this
  have hψk : ψ (g * ↑k) = ψ g := by
    have := congrFun (congrArg RightTranslationFn.toFun hk.2) g
    simp only [RightTranslationFn.toFun_smul] at this
    exact this
  simp only [RightTranslationFn.toFun_smul]
  exact congrArg₂ (· * ·) hφk hψk

theorem isKfSmooth_fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hηKf : IsKfSmooth F (chiDet (𝓞 F) F η)) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsKfSmooth F φ) : IsKfSmooth F (fnTwist F η φ) :=
  isSmoothVector_rightTranslationFn_mul hηKf hφ

theorem twistedCentralChar_one (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) :
    twistedCentralChar F Z ξ 1 = ξ := by
  ext z; simp [twistedCentralChar]

theorem isIdeleClassChar_one : IsIdeleClassChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :=
  fun _ => rfl

end AutomorphicForm

end
