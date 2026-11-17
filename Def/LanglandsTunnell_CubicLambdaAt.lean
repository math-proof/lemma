module

public import Def.LanglandsTunnell_CubicLambda
public import Inductive.LanglandsTunnell_ResolventDatum

@[expose] public section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg
open LanglandsTunnell.Converse AutomorphicForm HeckeCharacter

namespace LanglandsTunnell.CubicLambda

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

noncomputable def lambdaAt : ResolventDatum K → HeightOneSpectrum (𝓞 ℚ) → ℂ
  | @ResolventDatum.s3 _ _ _ _ _ L iF iN iA iI ω θ _ _ _ _ _ _ _ _ _, p => by
      letI := iF
      letI := iN
      letI := iA
      letI := iI
      exact stdRootNumberAt ℚ p (localChar ω p) *
        ∏ᶠ u ∈ primeFibre ℚ L p, stdRootNumberAt L u (localChar θ u)
  | .cyclic χ _ _ _ _, p =>
      stdRootNumberAt ℚ p (localChar χ p) * stdRootNumberAt ℚ p (localChar (χ ^ 2) p)

noncomputable def lambdaFin (Λd : ResolventDatum K) (w : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal = 1 ∧
      (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal = 1 then 1
  else lambdaAt K Λd (w.under (𝓞 ℚ))

end LanglandsTunnell.CubicLambda

end
