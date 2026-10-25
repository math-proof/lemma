import Mathlib
import Instance.ModularForm_KatzLevelOne
import Lemma.ModularCurve.KatzLevelP

set_option autoImplicit false

universe u

noncomputable section

open WeierstrassCurve

@[reducible] def KatzModularForm.algebraThrough (R₀ : Type u) [CommRing R₀] (R₁ : Type u)
    [CommRing R₁] [Algebra R₀ R₁] (A : Type u) [CommRing A] [Algebra R₁ A] : Algebra R₀ A :=
  ((algebraMap R₁ A).comp (algebraMap R₀ R₁)).toAlgebra

theorem KatzModularForm.algebraThrough_eq (R₀ : Type u) [CommRing R₀] (R₁ : Type u) [CommRing R₁]
    [Algebra R₀ R₁] (A : Type u) [CommRing A] [Algebra R₁ A] [h : Algebra R₀ A]
    [IsScalarTower R₀ R₁ A] : KatzModularForm.algebraThrough R₀ R₁ A = h :=
  Algebra.algebra_ext _ _ fun r => (IsScalarTower.algebraMap_apply R₀ R₁ A r).symm

def KatzModularForm.algHomThrough (R₀ : Type u) [CommRing R₀] (R₁ : Type u) [CommRing R₁]
    [Algebra R₀ R₁] {A B : Type u} [CommRing A] [Algebra R₁ A] [CommRing B] [Algebra R₁ B]
    (f : A →ₐ[R₁] B) :
    letI := KatzModularForm.algebraThrough R₀ R₁ A
    letI := KatzModularForm.algebraThrough R₀ R₁ B
    A →ₐ[R₀] B :=
  letI := KatzModularForm.algebraThrough R₀ R₁ A
  letI := KatzModularForm.algebraThrough R₀ R₁ B
  { (f : A →+* B) with
    commutes' := fun r => by
      show f ((algebraMap R₁ A) (algebraMap R₀ R₁ r)) = (algebraMap R₁ B) (algebraMap R₀ R₁ r)
      exact f.commutes _ }

namespace KatzModularForm

variable {R₀ : Type u} [CommRing R₀] {k : ℤ}

def baseChange (g : KatzModularForm R₀ k) (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁] :
    KatzModularForm R₁ k where
  toFun A _ _ W hW := @KatzModularForm.toFun R₀ _ k g A _ (algebraThrough R₀ R₁ A) W hW
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    exact @KatzModularForm.map_toFun R₀ _ k g A B _ (algebraThrough R₀ R₁ A) _
      (algebraThrough R₀ R₁ B) (algHomThrough R₀ R₁ f) W hW hW'
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    exact @KatzModularForm.toFun_variableChange R₀ _ k g A _ (algebraThrough R₀ R₁ A) C W hW hW'

variable (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁]

theorem baseChange_toFun' (g : KatzModularForm R₀ k) {A : Type u} [CommRing A] [Algebra R₁ A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (g.baseChange R₁).toFun W hW =
      @KatzModularForm.toFun R₀ _ k g A _ (algebraThrough R₀ R₁ A) W hW := rfl

theorem baseChange_toFun (g : KatzModularForm R₀ k) {A : Type u} [CommRing A] [Algebra R₀ A]
    [Algebra R₁ A] [IsScalarTower R₀ R₁ A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (g.baseChange R₁).toFun W hW = g.toFun W hW := by
  rw [baseChange_toFun', algebraThrough_eq R₀ R₁ A]

@[simp] theorem baseChange_zero : (0 : KatzModularForm R₀ k).baseChange R₁ = 0 := rfl

@[simp] theorem baseChange_add (g h : KatzModularForm R₀ k) :
    (g + h).baseChange R₁ = g.baseChange R₁ + h.baseChange R₁ := rfl

@[simp] theorem baseChange_neg (g : KatzModularForm R₀ k) : (-g).baseChange R₁ = -g.baseChange R₁ :=
  rfl

@[simp] theorem baseChange_sub (g h : KatzModularForm R₀ k) :
    (g - h).baseChange R₁ = g.baseChange R₁ - h.baseChange R₁ := rfl

@[simp] theorem baseChange_smul (c : R₀) (g : KatzModularForm R₀ k) :
    (c • g).baseChange R₁ = algebraMap R₀ R₁ c • g.baseChange R₁ := by
  ext A _ _ W hW
  letI := algebraThrough R₀ R₁ A
  show (c • g).toFun W hW = algebraMap R₀ R₁ c • g.toFun W hW
  rw [smul_toFun, Algebra.smul_def, Algebra.smul_def]
  rfl

theorem baseChange_mul {l : ℤ} (g : KatzModularForm R₀ k) (h : KatzModularForm R₀ l) :
    (g.mul h).baseChange R₁ = (g.baseChange R₁).mul (h.baseChange R₁) := rfl

end KatzModularForm

namespace ModularCurve

namespace KatzLevelPForm

open KatzModularForm (algebraThrough algebraThrough_eq algHomThrough)

variable {R₀ : Type u} [CommRing R₀] {p : ℕ} {k : ℤ}

def baseChange (F : KatzLevelPForm R₀ p k) (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁] :
    KatzLevelPForm R₁ p k where
  toFun A _ _ W hW D hD := @KatzLevelPForm.toFun R₀ _ p k F A _ (algebraThrough R₀ R₁ A) W hW D hD
  map_toFun := by
    intro A B _ _ _ _ f W hW hW' D hD hD'
    exact @KatzLevelPForm.map_toFun R₀ _ p k F A B _ (algebraThrough R₀ R₁ A) _
      (algebraThrough R₀ R₁ B) (algHomThrough R₀ R₁ f) W hW hW' D hD hD'
  toFun_variableChange := by
    intro A _ _ C W hW hW' D hD hD'
    exact @KatzLevelPForm.toFun_variableChange R₀ _ p k F A _ (algebraThrough R₀ R₁ A) C W hW hW'
      D hD hD'

variable (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁]

theorem baseChange_toFun' (F : KatzLevelPForm R₀ p k) {A : Type u} [CommRing A] [Algebra R₁ A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) :
    (F.baseChange R₁).toFun W hW D hD =
      @KatzLevelPForm.toFun R₀ _ p k F A _ (algebraThrough R₀ R₁ A) W hW D hD := rfl

theorem baseChange_toFun (F : KatzLevelPForm R₀ p k) {A : Type u} [CommRing A] [Algebra R₀ A]
    [Algebra R₁ A] [IsScalarTower R₀ R₁ A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D : LevelPData A) (hD : IsLevelPStructure W p D) :
    (F.baseChange R₁).toFun W hW D hD = F.toFun W hW D hD := by
  rw [baseChange_toFun', algebraThrough_eq R₀ R₁ A]

@[simp] theorem baseChange_zero : (0 : KatzLevelPForm R₀ p k).baseChange R₁ = 0 := rfl

@[simp] theorem baseChange_add (F G : KatzLevelPForm R₀ p k) :
    (F + G).baseChange R₁ = F.baseChange R₁ + G.baseChange R₁ := rfl

@[simp] theorem baseChange_neg (F : KatzLevelPForm R₀ p k) :
    (-F).baseChange R₁ = -F.baseChange R₁ := rfl

@[simp] theorem baseChange_sub (F G : KatzLevelPForm R₀ p k) :
    (F - G).baseChange R₁ = F.baseChange R₁ - G.baseChange R₁ := rfl

@[simp] theorem baseChange_smul (c : R₀) (F : KatzLevelPForm R₀ p k) :
    (c • F).baseChange R₁ = algebraMap R₀ R₁ c • F.baseChange R₁ := by
  ext A _ _ W hW D hD
  letI := algebraThrough R₀ R₁ A
  show (c • F).toFun W hW D hD = algebraMap R₀ R₁ c • F.toFun W hW D hD
  rw [smul_toFun, Algebra.smul_def, Algebra.smul_def]
  rfl

theorem baseChange_mul {l : ℤ} (F : KatzLevelPForm R₀ p k) (G : KatzLevelPForm R₀ p l) :
    (F.mul G).baseChange R₁ = (F.baseChange R₁).mul (G.baseChange R₁) := rfl

@[simp] theorem baseChange_swap (F : KatzLevelPForm R₀ p k) :
    F.swap.baseChange R₁ = (F.baseChange R₁).swap := rfl

theorem DependsOnlyOnSndLine.baseChange {F : KatzLevelPForm R₀ p k} (h : F.DependsOnlyOnSndLine) :
    (F.baseChange R₁).DependsOnlyOnSndLine :=
  fun A _ _ W hW D D' hD hD' hQ =>
    @h A _ (algebraThrough R₀ R₁ A) W hW D D' hD hD' hQ

theorem DependsOnlyOnLines.baseChange {F : KatzLevelPForm R₀ p k} (h : F.DependsOnlyOnLines) :
    (F.baseChange R₁).DependsOnlyOnLines :=
  fun A _ _ W hW D D' hD hD' hP hQ =>
    @h A _ (algebraThrough R₀ R₁ A) W hW D D' hD hD' hP hQ

theorem SwapInvariant.baseChange {F : KatzLevelPForm R₀ p k} (h : F.SwapInvariant) :
    (F.baseChange R₁).SwapInvariant :=
  fun A _ _ W hW D hD => @h A _ (algebraThrough R₀ R₁ A) W hW D hD

end KatzLevelPForm

namespace KatzGamma0Form

variable {R₀ : Type u} [CommRing R₀] {p : ℕ} {k : ℤ}

def baseChange (φ : KatzGamma0Form R₀ p k) (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁] :
    KatzGamma0Form R₁ p k :=
  ⟨φ.toKatzLevelPForm.baseChange R₁, φ.dependsOnlyOnSndLine.baseChange R₁⟩

variable (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁]

@[simp] theorem baseChange_toKatzLevelPForm (φ : KatzGamma0Form R₀ p k) :
    (φ.baseChange R₁).toKatzLevelPForm = φ.toKatzLevelPForm.baseChange R₁ := rfl

@[simp] theorem baseChange_zero : (0 : KatzGamma0Form R₀ p k).baseChange R₁ = 0 := rfl

@[simp] theorem baseChange_add (φ ψ : KatzGamma0Form R₀ p k) :
    (φ + ψ).baseChange R₁ = φ.baseChange R₁ + ψ.baseChange R₁ := rfl

@[simp] theorem baseChange_neg (φ : KatzGamma0Form R₀ p k) :
    (-φ).baseChange R₁ = -φ.baseChange R₁ := rfl

@[simp] theorem baseChange_sub (φ ψ : KatzGamma0Form R₀ p k) :
    (φ - ψ).baseChange R₁ = φ.baseChange R₁ - ψ.baseChange R₁ := rfl

@[simp] theorem baseChange_smul (c : R₀) (φ : KatzGamma0Form R₀ p k) :
    (c • φ).baseChange R₁ = algebraMap R₀ R₁ c • φ.baseChange R₁ := by
  ext1; simp

end KatzGamma0Form

end ModularCurve

namespace KatzModularForm

variable {R₀ : Type u} [CommRing R₀] {k : ℤ} (R₁ : Type u) [CommRing R₁] [Algebra R₀ R₁]

theorem pullbackLevelP_baseChange (g : KatzModularForm R₀ k) (p : ℕ) :
    (g.baseChange R₁).pullbackLevelP p = (g.pullbackLevelP p).baseChange R₁ := rfl

theorem pullbackGamma0_baseChange (g : KatzModularForm R₀ k) (p : ℕ) :
    (g.baseChange R₁).pullbackGamma0 p = (g.pullbackGamma0 p).baseChange R₁ := rfl

end KatzModularForm

end
