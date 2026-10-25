-- Carved from Lemma/Definitions/Def_LocalNewvector_PrincipalSeriesCarrier.lean: instance decls only.
import Lemma.LocalNewvector.ConductorDatum
import Lemma.LocalNewvector.PrincipalSeriesCarrier

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

variable (p : ℕ) [Fact p.Prime]


section PrincipalSeriesCarrier

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

namespace PSCarrier

instance : AddCommGroup (PSCarrier p μ₁ μ₂) :=
  inferInstanceAs (AddCommGroup ↥(principalSeries p μ₁ μ₂))

instance : Module ℂ (PSCarrier p μ₁ μ₂) :=
  inferInstanceAs (Module ℂ ↥(principalSeries p μ₁ μ₂))

instance : DistribMulAction (GL (Fin 2) ℚ_[p]) (PSCarrier p μ₁ μ₂) where
  smul g f := mk p μ₁ μ₂
    ⟨fun y => toFn p μ₁ μ₂ f (y * g),
     rightTranslate_mem_principalSeries p (toFn_mem p μ₁ μ₂ f) g⟩
  one_smul f := ext p μ₁ μ₂ fun y => congrArg (toFn p μ₁ μ₂ f) (mul_one y)
  mul_smul g h f := ext p μ₁ μ₂ fun y => congrArg (toFn p μ₁ μ₂ f) (mul_assoc y g h).symm
  smul_zero _ := ext p μ₁ μ₂ fun _ => rfl
  smul_add _ _ _ := ext p μ₁ μ₂ fun _ => rfl

instance : SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ (PSCarrier p μ₁ μ₂) where
  smul_comm _ _ _ := ext p μ₁ μ₂ fun _ => rfl

end PSCarrier

end PrincipalSeriesCarrier

end LocalNewvector

end
