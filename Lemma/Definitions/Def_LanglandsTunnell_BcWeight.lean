import Lemma.Definitions.Def_AutomorphicForm_FormalBaseChange

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField IsDedekindDomain

variable (F K : Type) [Field F] [Field K] [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  {R : Type*} [CommRing R]

noncomputable def bcWeight (χ : HeightOneSpectrum (𝓞 F) → R) : HeightOneSpectrum (𝓞 K) → R :=
  fun 𝔓 => χ (𝔓.under (𝓞 F)) ^ (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal

@[simp] theorem bcWeight_apply (χ : HeightOneSpectrum (𝓞 F) → R) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    bcWeight F K χ 𝔓 = χ (𝔓.under (𝓞 F)) ^ (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal :=
  rfl

end LanglandsTunnell
