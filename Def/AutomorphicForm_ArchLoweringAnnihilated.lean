import Mathlib
import Def.AutomorphicForm_ViaCompactCuspNotion

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

noncomputable section

namespace AutomorphicForm

def loweringAt (f : (Fin 2 → Fin 2 → ℝ) → ℂ) (m : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (fderiv ℝ f m (m * !![1, 0; 0, -1]) - Complex.I * fderiv ℝ f m (m * !![0, 1; 1, 0])) / 2


variable {F : Type} [Field F] [NumberField F]

def archSliceAt (w : InfinitePlace F) (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) (m : Fin 2 → Fin 2 → ℝ) : ℂ :=
  if h : (Matrix.of m).det ≠ 0 then
    φ (g * adelicArchGLInclAt F w
      (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
        (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of m) h)))
  else 0


def IsArchLoweringAnnihilatedAt (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (g : AdelicGL2 (𝓞 F) F) (z : UpperHalfPlane),
    DifferentiableAt ℝ (archSliceAt w hw φ g) (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) ∧
      loweringAt (archSliceAt w hw φ g) !![z.im, z.re; 0, 1] = 0

end AutomorphicForm

end
