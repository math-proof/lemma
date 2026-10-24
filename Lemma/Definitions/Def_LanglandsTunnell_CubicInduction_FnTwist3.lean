import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Carrier

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section DetCharacter

variable (n : ℕ) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def chiDetGL (η : (AdeleRing R K)ˣ →* ℂˣ) : AdelicGL n R K → ℂ :=
  fun g => ((η (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)

theorem chiDetGL_apply (η : (AdeleRing R K)ˣ →* ℂˣ) (g : AdelicGL n R K) :
    chiDetGL n R K η g = ((η (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := rfl

theorem chiDetGL_one (g : AdelicGL n R K) : chiDetGL n R K (1 : (AdeleRing R K)ˣ →* ℂˣ) g = 1 := by
  simp [chiDetGL]

theorem chiDetGL_mul_apply (η₁ η₂ : (AdeleRing R K)ˣ →* ℂˣ) (g : AdelicGL n R K) :
    chiDetGL n R K (η₁ * η₂) g = chiDetGL n R K η₁ g * chiDetGL n R K η₂ g := by
  simp [chiDetGL]

theorem chiDetGL_mul (η : (AdeleRing R K)ˣ →* ℂˣ) (g h : AdelicGL n R K) :
    chiDetGL n R K η (g * h) = chiDetGL n R K η g * chiDetGL n R K η h := by
  simp [chiDetGL, map_mul]

theorem chiDetGL_ne_zero (η : (AdeleRing R K)ˣ →* ℂˣ) (g : AdelicGL n R K) : chiDetGL n R K η g ≠ 0 :=
  (η (Matrix.GeneralLinearGroup.det g)).ne_zero

theorem norm_chiDetGL_eq_one {η : (AdeleRing R K)ˣ →* ℂˣ} (hη : AutomorphicForm.IsUnitaryChar R K η)
    (g : AdelicGL n R K) : ‖chiDetGL n R K η g‖ = 1 :=
  hη _

theorem det_centralScalarGL (z : (AdeleRing R K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalarGL n R K z) = z ^ n := by
  rw [show centralScalarGL n R K = Matrix.GeneralLinearGroup.scalar (Fin n) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem chiDetGL_centralScalarGL_mul (η : (AdeleRing R K)ˣ →* ℂˣ) (z : (AdeleRing R K)ˣ)
    (g : AdelicGL n R K) :
    chiDetGL n R K η (centralScalarGL n R K z * g) = ((η z : ℂˣ) : ℂ) ^ n * chiDetGL n R K η g := by
  simp only [chiDetGL, map_mul, det_centralScalarGL, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]

theorem det_globalPointsGL (γ : Matrix.GeneralLinearGroup (Fin n) K) :
    Matrix.GeneralLinearGroup.det (globalPointsGL n R K γ) =
      Units.map (algebraMap K (AdeleRing R K)) (Matrix.GeneralLinearGroup.det γ) :=
  Matrix.GeneralLinearGroup.map_det _ _

theorem chiDetGL_globalPointsGL_mul {η : (AdeleRing R K)ˣ →* ℂˣ}
    (hη : AutomorphicForm.IsIdeleClassChar R K η) (γ : Matrix.GeneralLinearGroup (Fin n) K)
    (g : AdelicGL n R K) : chiDetGL n R K η (globalPointsGL n R K γ * g) = chiDetGL n R K η g := by
  unfold chiDetGL
  congr 1
  rw [map_mul, det_globalPointsGL, map_mul, hη (Matrix.GeneralLinearGroup.det γ), one_mul]

end DetCharacter

section DetUnipotent

variable {A : Type*} [CommRing A]

theorem det_upperUnipotent3 (x y z : A) : Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z) = 1 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_three]

theorem det_radicalP21 (v : Fin 2 → A) : Matrix.GeneralLinearGroup.det (radicalP21 v) = 1 :=
  det_upperUnipotent3 _ _ _

theorem det_radicalP12 (v : Fin 2 → A) : Matrix.GeneralLinearGroup.det (radicalP12 v) = 1 :=
  det_upperUnipotent3 _ _ _

end DetUnipotent

section DetCharacterThree

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem chiDetGL_three_centralScalarGL_mul (η : (AdeleRing R K)ˣ →* ℂˣ) (z : (AdeleRing R K)ˣ)
    (g : AdelicGL 3 R K) :
    chiDetGL 3 R K η (centralScalarGL 3 R K z * g) = ((η z : ℂˣ) : ℂ) ^ 3 * chiDetGL 3 R K η g :=
  chiDetGL_centralScalarGL_mul 3 R K η z g

theorem chiDetGL_upperUnipotent3_mul (η : (AdeleRing R K)ˣ →* ℂˣ) (x y z : AdeleRing R K)
    (g : AdelicGL 3 R K) : chiDetGL 3 R K η (upperUnipotent3 x y z * g) = chiDetGL 3 R K η g := by
  simp [chiDetGL, map_mul, det_upperUnipotent3]

theorem chiDetGL_radicalP21_mul (η : (AdeleRing R K)ˣ →* ℂˣ) (v : Fin 2 → AdeleRing R K)
    (g : AdelicGL 3 R K) : chiDetGL 3 R K η (radicalP21 v * g) = chiDetGL 3 R K η g := by
  simp [chiDetGL, map_mul, det_radicalP21]

theorem chiDetGL_radicalP12_mul (η : (AdeleRing R K)ˣ →* ℂˣ) (v : Fin 2 → AdeleRing R K)
    (g : AdelicGL 3 R K) : chiDetGL 3 R K η (radicalP12 v * g) = chiDetGL 3 R K η g := by
  simp [chiDetGL, map_mul, det_radicalP12]

end DetCharacterThree

section Twist

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def fnTwist3 (η : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL 3 R K → ℂ) : AdelicGL 3 R K → ℂ :=
  fun g => chiDetGL 3 R K η g * φ g

@[simp] theorem fnTwist3_apply (η : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL 3 R K → ℂ) (g : AdelicGL 3 R K) :
    fnTwist3 R K η φ g = chiDetGL 3 R K η g * φ g := rfl

theorem fnTwist3_zero (η : (AdeleRing R K)ˣ →* ℂˣ) : fnTwist3 R K η (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  ext g; simp [fnTwist3]

theorem fnTwist3_one (φ : AdelicGL 3 R K → ℂ) : fnTwist3 R K (1 : (AdeleRing R K)ˣ →* ℂˣ) φ = φ := by
  ext g; simp [fnTwist3, chiDetGL]

theorem fnTwist3_fnTwist3 (η₁ η₂ : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL 3 R K → ℂ) :
    fnTwist3 R K η₁ (fnTwist3 R K η₂ φ) = fnTwist3 R K (η₁ * η₂) φ := by
  ext g; simp only [fnTwist3, chiDetGL, MonoidHom.mul_apply, Units.val_mul]; ring

def twistedCentralChar3 (ω η : (AdeleRing R K)ˣ →* ℂˣ) : (AdeleRing R K)ˣ →* ℂˣ :=
  ω * η ^ 3

theorem twistedCentralChar3_apply (ω η : (AdeleRing R K)ˣ →* ℂˣ) (z : (AdeleRing R K)ˣ) :
    (twistedCentralChar3 R K ω η z : ℂ) = (ω z : ℂ) * (η z : ℂ) ^ 3 := by
  simp only [twistedCentralChar3, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]

theorem twistedCentralChar3_one (ω : (AdeleRing R K)ˣ →* ℂˣ) : twistedCentralChar3 R K ω 1 = ω := by
  ext z; simp [twistedCentralChar3]

theorem isIdeleClassChar_twistedCentralChar3 {ω η : (AdeleRing R K)ˣ →* ℂˣ}
    (hω : AutomorphicForm.IsIdeleClassChar R K ω) (hη : AutomorphicForm.IsIdeleClassChar R K η) :
    AutomorphicForm.IsIdeleClassChar R K (twistedCentralChar3 R K ω η) := fun u => by
  simp only [twistedCentralChar3, MonoidHom.mul_apply, MonoidHom.pow_apply, hω u, hη u, one_pow, mul_one]

theorem fnTwist3_centralScalarGL_mul (ω η : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL 3 R K → ℂ)
    (z : (AdeleRing R K)ˣ) (g : AdelicGL 3 R K) (hφ : φ (centralScalarGL 3 R K z * g) = (ω z : ℂ) * φ g) :
    fnTwist3 R K η φ (centralScalarGL 3 R K z * g) = (twistedCentralChar3 R K ω η z : ℂ) * fnTwist3 R K η φ g := by
  simp only [fnTwist3_apply, chiDetGL_three_centralScalarGL_mul, hφ, twistedCentralChar3_apply]; ring

end Twist

end LanglandsTunnell.CubicInduction

end
