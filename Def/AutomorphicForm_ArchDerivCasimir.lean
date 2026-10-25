import Lemma.AutomorphicForm.ArchType
import Lemma.AutomorphicForm.ArchWeightCharTransport
import Lemma.LanglandsTunnell.ArchParam
import Def.AutomorphicForm_ConstantTerm
import Inductive.AutomorphicForm_ArchDir

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.RealArchParam

def laplaceEigenvalue : RealArchParam → ℂ
  | principal u₁ _ u₂ _ => 1 / 4 - ((u₁ - u₂) / 2) ^ 2
  | discrete _ k _ => (1 - (k : ℂ) ^ 2) / 4

end LanglandsTunnell.RealArchParam

namespace AutomorphicForm

open NumberField NumberField.InfinitePlace.Completion Matrix

variable (F : Type) [Field F] [NumberField F]

section RealPlaceTransport

variable {F}

def archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) : GL (Fin 2) ℝ →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLInclAt F w).comp (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).toMonoidHom

def archRealLiftAt {w : InfinitePlace F} (hw : w.IsReal) (e : Fin 2 → Fin 2 → ℝ) : AdelicGL2 (𝓞 F) F :=
  if h : (Matrix.of e).det ≠ 0 then archRealGLAt hw (GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h)
  else 1


def IsArchSmoothAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F,
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e))
      {e | (Matrix.of e).det ≠ 0}

end RealPlaceTransport

section Flows

variable {F}

def lowerUnipotentGL2 {R : Type*} [CommRing R] (x : R) : GL (Fin 2) R where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]


def splitTorusGL2 (t : ℝ) : GL (Fin 2) ℝ where
  val := !![Real.exp t, 0; 0, Real.exp (-t)]
  inv := !![Real.exp (-t), 0; 0, Real.exp t]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]


def archFlowMatrix : ArchDir → ℝ → GL (Fin 2) ℝ
  | .H, t => splitTorusGL2 t
  | .E, t => unipotentGL2 t
  | .Fm, t => lowerUnipotentGL2 t


def archFlowAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) : AdelicGL2 (𝓞 F) F :=
  archRealGLAt hw (archFlowMatrix d t)


def archDerivAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => deriv (fun t : ℝ => φ (g * archFlowAt hw d t)) 0

def archCasimirAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  -((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H φ) - (1 / 2 : ℂ) • archDerivAt hw .H φ +
    archDerivAt hw .E (archDerivAt hw .Fm φ))


def archDirMatrix : ArchDir → Matrix (Fin 2) (Fin 2) ℝ
  | .H => !![1, 0; 0, -1]
  | .E => !![0, 1; 0, 0]
  | .Fm => !![0, 0; 1, 0]


def archRealProjAt {w : InfinitePlace F} (hw : w.IsReal) : AdelicGL2 (𝓞 F) F →* GL (Fin 2) ℝ :=
  (glEquivOfRingEquiv (ringEquivRealOfIsReal hw)).toMonoidHom.comp
    ((AdelicLevel.archComponent F w).comp (AdelicLevel.glArch (𝓞 F) F))

end Flows

end AutomorphicForm

end
