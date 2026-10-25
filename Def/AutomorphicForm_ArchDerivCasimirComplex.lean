import Def.AutomorphicForm_ArchDerivCasimir
import Inductive.AutomorphicForm_ArchDirComplex

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

open NumberField NumberField.InfinitePlace.Completion Matrix Complex

variable (F : Type) [Field F] [NumberField F]

section ComplexPlaceTransport

variable {F}

def archComplexGLAt {w : InfinitePlace F} (hw : w.IsComplex) : GL (Fin 2) ℂ →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLInclAt F w).comp (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm).toMonoidHom

def archComplexLiftAt {w : InfinitePlace F} (hw : w.IsComplex) (e : Fin 2 → Fin 2 → ℂ) : AdelicGL2 (𝓞 F) F :=
  if h : (Matrix.of e).det ≠ 0 then archComplexGLAt hw (GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h) else 1


def IsArchSmoothAtComplex {w : InfinitePlace F} (hw : w.IsComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F,
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
      {e | (Matrix.of e).det ≠ 0}

end ComplexPlaceTransport

section ComplexFlows

variable {F}

def ArchDir.toComplex : ArchDir → ArchDirComplex
  | .H => .H
  | .E => .E
  | .Fm => .Fm

def ArchDir.toComplexI : ArchDir → ArchDirComplex
  | .H => .iH
  | .E => .iE
  | .Fm => .iFm

def splitTorusGL2Complex (z : ℂ) : GL (Fin 2) ℂ where
  val := !![Complex.exp z, 0; 0, Complex.exp (-z)]
  inv := !![Complex.exp (-z), 0; 0, Complex.exp z]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]


def archFlowMatrixComplex : ArchDirComplex → ℝ → GL (Fin 2) ℂ
  | .H, t => splitTorusGL2Complex (t : ℂ)
  | .E, t => unipotentGL2 (t : ℂ)
  | .Fm, t => lowerUnipotentGL2 (t : ℂ)
  | .iH, t => splitTorusGL2Complex ((t : ℂ) * I)
  | .iE, t => unipotentGL2 ((t : ℂ) * I)
  | .iFm, t => lowerUnipotentGL2 ((t : ℂ) * I)


def archFlowAtComplex {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) (t : ℝ) : AdelicGL2 (𝓞 F) F :=
  archComplexGLAt hw (archFlowMatrixComplex d t)


def archDerivAtComplex {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => deriv (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) 0

def archDelAt {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  (1 / 2 : ℂ) • (archDerivAtComplex hw d.toComplex φ - I • archDerivAtComplex hw d.toComplexI φ)

def archDelBarAt {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  (1 / 2 : ℂ) • (archDerivAtComplex hw d.toComplex φ + I • archDerivAtComplex hw d.toComplexI φ)

def archCasimirAtComplex {w : InfinitePlace F} (hw : w.IsComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  -((1 / 4 : ℂ) • archDelAt hw .H (archDelAt hw .H φ) - (1 / 2 : ℂ) • archDelAt hw .H φ +
    archDelAt hw .E (archDelAt hw .Fm φ))

def archCasimirBarAtComplex {w : InfinitePlace F} (hw : w.IsComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  -((1 / 4 : ℂ) • archDelBarAt hw .H (archDelBarAt hw .H φ) - (1 / 2 : ℂ) • archDelBarAt hw .H φ +
    archDelBarAt hw .E (archDelBarAt hw .Fm φ))

def archKCasimirAtComplex {w : InfinitePlace F} (hw : w.IsComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) +
    (archDerivAtComplex hw .E (archDerivAtComplex hw .E φ - archDerivAtComplex hw .Fm φ) -
      archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ - archDerivAtComplex hw .Fm φ)) +
    (archDerivAtComplex hw .iE (archDerivAtComplex hw .iE φ + archDerivAtComplex hw .iFm φ) +
      archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ + archDerivAtComplex hw .iFm φ))

end ComplexFlows

section Circle

variable {F}

def circleGL2 (ζ : ℂˣ) : GL (Fin 2) ℂ where
  val := !![(ζ : ℂ), 0; 0, ((ζ⁻¹ : ℂˣ) : ℂ)]
  inv := !![((ζ⁻¹ : ℂˣ) : ℂ), 0; 0, (ζ : ℂ)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def archCircleAt {w : InfinitePlace F} (hw : w.IsComplex) (ζ : ℂˣ) : AdelicGL2 (𝓞 F) F :=
  archComplexGLAt hw (circleGL2 ζ)

def HasCircleWeightAt {w : InfinitePlace F} (hw : w.IsComplex) (m : ℤ) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ g : AdelicGL2 (𝓞 F) F, φ (g * archCircleAt hw ζ) = (ζ : ℂ) ^ m * φ g

end Circle

end AutomorphicForm

end
