import Def.LanglandsTunnell_DeltaLift
import Lemma.AdelicDock.LocalEmbedding

set_option autoImplicit false

noncomputable section

namespace CuspForm

variable {M : ℕ}

open scoped ModularForm in

def IsAdelicLiftOfGamma1 (g : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) : Prop :=
  (∀ (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      φ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = φ x) ∧
    (∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel M),
      ∀ x, φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = φ x) ∧
    ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
          φ h = ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I

end CuspForm

end
