-- Carved from Lemma/Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean: instance decls only.

open NumberField MeasureTheory AutomorphicForm

noncomputable section

namespace LocalNewvector

variable (F : Type*) [Field F] [NumberField F]


namespace AdelicFnCarrier

variable {F}


instance : AddCommGroup (AdelicFnCarrier F) :=
  inferInstanceAs (AddCommGroup (AdelicGL2 (𝓞 F) F → ℂ))

instance : Module ℂ (AdelicFnCarrier F) :=
  inferInstanceAs (Module ℂ (AdelicGL2 (𝓞 F) F → ℂ))


instance : DistribMulAction (AdelicGL2 (𝓞 F) F) (AdelicFnCarrier F) where
  smul g φ := mk fun x => φ.toFn (x * g)
  one_smul φ := ext fun x => congrArg φ.toFn (mul_one x)
  mul_smul g h φ := ext fun x => congrArg φ.toFn (mul_assoc x g h).symm
  smul_zero _ := ext fun _ => rfl
  smul_add _ _ _ := ext fun _ => rfl


instance : SMulCommClass ℂ (AdelicGL2 (𝓞 F) F) (AdelicFnCarrier F) where
  smul_comm _ _ _ := ext fun _ => rfl

instance : SMulCommClass (AdelicGL2 (𝓞 F) F) ℂ (AdelicFnCarrier F) :=
  SMulCommClass.symm _ _ _


end AdelicFnCarrier

variable {F}


namespace AdelicSpan

variable (φ : AdelicGL2 (𝓞 F) F → ℂ)


instance : AddCommGroup (AdelicSpan φ) :=
  inferInstanceAs (AddCommGroup (AdelicSpanSubmodule φ))

instance : Module ℂ (AdelicSpan φ) :=
  inferInstanceAs (Module ℂ (AdelicSpanSubmodule φ))

instance : DistribMulAction (AdelicGL2 (𝓞 F) F) (AdelicSpan φ) where
  smul g ψ := mk φ (g • toFn φ ψ)
    (smul_mem_adelicSpanSubmodule φ g (ψ : AdelicSpanSubmodule φ).2)
  one_smul ψ := ext φ (one_smul (AdelicGL2 (𝓞 F) F) (toFn φ ψ))
  mul_smul g h ψ := ext φ (mul_smul (α := AdelicGL2 (𝓞 F) F) g h (toFn φ ψ))
  smul_zero g := ext φ (smul_zero (A := AdelicFnCarrier F) g)
  smul_add g ψ₁ ψ₂ := ext φ (smul_add (A := AdelicFnCarrier F) g (toFn φ ψ₁) (toFn φ ψ₂))


instance : SMulCommClass ℂ (AdelicGL2 (𝓞 F) F) (AdelicSpan φ) where
  smul_comm c g ψ := ext φ (smul_comm (α := AdelicFnCarrier F) c g (toFn φ ψ))

instance : SMulCommClass (AdelicGL2 (𝓞 F) F) ℂ (AdelicSpan φ) :=
  SMulCommClass.symm _ _ _


end AdelicSpan

variable (F)


section PadicAction

variable (p : ℕ) [Fact p.Prime]

instance : DistribMulAction (GL (Fin 2) ℚ_[p]) (AdelicFnCarrier ℚ) :=
  DistribMulAction.compHom _ (AdelicDock.padicToAdelic p)


instance : SMulCommClass ℂ (GL (Fin 2) ℚ_[p]) (AdelicFnCarrier ℚ) where
  smul_comm c g φ := smul_comm (α := AdelicFnCarrier ℚ) c (AdelicDock.padicToAdelic p g) φ

instance : SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ (AdelicFnCarrier ℚ) :=
  SMulCommClass.symm _ _ _

variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

instance : DistribMulAction (GL (Fin 2) ℚ_[p]) (AdelicSpan φ) :=
  DistribMulAction.compHom _ (AdelicDock.padicToAdelic p)


instance : SMulCommClass ℂ (GL (Fin 2) ℚ_[p]) (AdelicSpan φ) where
  smul_comm c g ψ := smul_comm (α := AdelicSpan φ) c (AdelicDock.padicToAdelic p g) ψ

instance : SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ (AdelicSpan φ) :=
  SMulCommClass.symm _ _ _


end PadicAction

end LocalNewvector

end
