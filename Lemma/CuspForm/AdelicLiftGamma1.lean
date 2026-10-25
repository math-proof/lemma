import Def.LanglandsTunnell_DeltaLift
import Lemma.AdelicDock.LocalEmbedding
import Def.CuspForm_AdelicLiftGamma1

set_option autoImplicit false

noncomputable section

namespace CuspForm

variable {M : ℕ}


theorem IsAdelicLiftOfGamma1.left_inv {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφg : IsAdelicLiftOfGamma1 g φ)
    (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    φ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = φ x :=
  hφg.1 γ x

theorem IsAdelicLiftOfGamma1.level_inv {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφg : IsAdelicLiftOfGamma1 g φ) :
    ∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel M),
      ∀ x, φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = φ x :=
  hφg.2.1

open scoped ModularForm in

theorem IsAdelicLiftOfGamma1.apply_eq {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφg : IsAdelicLiftOfGamma1 g φ)
    (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)
    (hfin : NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    φ h = ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I :=
  hφg.2.2 h hfin hpos

end CuspForm

end
