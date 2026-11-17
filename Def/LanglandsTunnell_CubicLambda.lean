module

public import Def.LanglandsTunnell_ConverseData
public import Def.LanglandsTunnell_RankinSelbergEuler
public import Def.HeckeCharacter_FiniteOrder
public import Structure.HeckeCharacter_FiniteOrder

@[expose] public section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg
open LanglandsTunnell.Converse AutomorphicForm HeckeCharacter

namespace LanglandsTunnell.CubicLambda

open scoped Classical in

noncomputable def eulerCoeff (F : Type) [Field F] [NumberField F] (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if IsUnramifiedCharAt η v then ((η (uniformizerIdele F v) : ℂˣ) : ℂ) else 0

noncomputable def zetaEulerPoly (F : Type) [Field F] [NumberField F] [Algebra (𝓞 ℚ) (𝓞 F)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 F)] (p : HeightOneSpectrum (𝓞 ℚ)) : Polynomial ℂ :=
  inducedEulerPoly ℚ (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) p

noncomputable def resolventSignBit (L : Type) [Field L] [NumberField L] : ZMod 2 :=
  if nrComplexPlaces L = 0 then 0 else 1


variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

open scoped Classical in
noncomputable def lambdaArch (w : InfinitePlace K) : ℂ :=
  if w.IsReal then 1 else signEpsilon 1

end LanglandsTunnell.CubicLambda

end
