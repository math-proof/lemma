import Mathlib
import Lemma.Definitions.Def_AutomorphicForm_ViaCompactCuspNotion

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

noncomputable section

namespace AutomorphicForm

def loweringAt (f : (Fin 2 → Fin 2 → ℝ) → ℂ) (m : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (fderiv ℝ f m (m * !![1, 0; 0, -1]) - Complex.I * fderiv ℝ f m (m * !![0, 1; 1, 0])) / 2

theorem loweringAt_eq (f : (Fin 2 → Fin 2 → ℝ) → ℂ) (m : Matrix (Fin 2) (Fin 2) ℝ) :
    loweringAt f m =
      (fderiv ℝ f m (m * !![1, 0; 0, -1]) - Complex.I * fderiv ℝ f m (m * !![0, 1; 1, 0])) / 2 :=
  rfl

theorem loweringAt_const (c : ℂ) (m : Matrix (Fin 2) (Fin 2) ℝ) :
    loweringAt (fun _ => c) m = 0 := by
  have h : fderiv ℝ (fun _ : Fin 2 → Fin 2 → ℝ => c) (m : Fin 2 → Fin 2 → ℝ) = 0 := by
    rw [fderiv_fun_const]
    rfl
  simp [loweringAt, h]

variable {F : Type} [Field F] [NumberField F]

def archSliceAt (w : InfinitePlace F) (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) (m : Fin 2 → Fin 2 → ℝ) : ℂ :=
  if h : (Matrix.of m).det ≠ 0 then
    φ (g * adelicArchGLInclAt F w
      (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
        (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of m) h)))
  else 0

theorem archSliceAt_apply_of_det_ne_zero (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (m : Fin 2 → Fin 2 → ℝ)
    (h : (Matrix.of m).det ≠ 0) :
    archSliceAt w hw φ g m =
      φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of m) h))) := by
  simp [archSliceAt, h]

theorem archSliceAt_apply_of_det_eq_zero (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (m : Fin 2 → Fin 2 → ℝ)
    (h : (Matrix.of m).det = 0) :
    archSliceAt w hw φ g m = 0 := by
  simp [archSliceAt, h]

theorem archSliceAt_coe_generalLinearGroup (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (m : GL (Fin 2) ℝ) :
    archSliceAt w hw φ g ((m : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) =
      φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom m)) := by
  have h : (Matrix.of ((m : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ)).det ≠ 0 := by
    have : Matrix.of ((m : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) = (m : Matrix _ _ ℝ) :=
      rfl
    rw [this, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det m).ne_zero
  rw [archSliceAt_apply_of_det_ne_zero w hw φ g _ h]
  congr 3
  ext i j
  rfl

theorem archSliceAt_iwasawa (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (z : UpperHalfPlane) :
    archSliceAt w hw φ g (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) =
      φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
          (iwasawaSectionGL z))) :=
  archSliceAt_coe_generalLinearGroup w hw φ g (iwasawaSectionGL z)

theorem archSliceAt_zero (w : InfinitePlace F) (hw : w.IsReal) (g : AdelicGL2 (𝓞 F) F) :
    archSliceAt w hw (fun _ => (0 : ℂ)) g = fun _ => 0 := by
  funext m
  by_cases h : (Matrix.of m).det ≠ 0
  · simp [archSliceAt, h]
  · simp [archSliceAt, h]

theorem archSliceAt_const_mul (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (a : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    archSliceAt w hw (fun x => a * φ x) g = fun m => a * archSliceAt w hw φ g m := by
  funext m
  by_cases h : (Matrix.of m).det ≠ 0
  · simp [archSliceAt, h]
  · simp [archSliceAt, h]

def IsArchLoweringAnnihilatedAt (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (g : AdelicGL2 (𝓞 F) F) (z : UpperHalfPlane),
    DifferentiableAt ℝ (archSliceAt w hw φ g) (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) ∧
      loweringAt (archSliceAt w hw φ g) !![z.im, z.re; 0, 1] = 0

theorem isArchLoweringAnnihilatedAt_iff (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsArchLoweringAnnihilatedAt w hw φ ↔
      ∀ (g : AdelicGL2 (𝓞 F) F) (z : UpperHalfPlane),
        DifferentiableAt ℝ (archSliceAt w hw φ g)
            (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) ∧
          loweringAt (archSliceAt w hw φ g) !![z.im, z.re; 0, 1] = 0 :=
  Iff.rfl

theorem isArchLoweringAnnihilatedAt_zero (w : InfinitePlace F) (hw : w.IsReal) :
    IsArchLoweringAnnihilatedAt w hw (fun _ => (0 : ℂ)) := by
  intro g z
  rw [archSliceAt_zero]
  exact ⟨differentiableAt_const _, loweringAt_const 0 _⟩

end AutomorphicForm

end

section Battery
open AutomorphicForm
#check @loweringAt
#check @archSliceAt
#check @IsArchLoweringAnnihilatedAt
#print axioms AutomorphicForm.loweringAt_const
#print axioms AutomorphicForm.archSliceAt_coe_generalLinearGroup
#print axioms AutomorphicForm.archSliceAt_iwasawa
#print axioms AutomorphicForm.archSliceAt_const_mul
#print axioms AutomorphicForm.isArchLoweringAnnihilatedAt_zero
end Battery
