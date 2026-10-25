import Def.LanglandsTunnell_CubicLambda

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg
open LanglandsTunnell.Converse AutomorphicForm HeckeCharacter

namespace LanglandsTunnell.CubicLambda

open scoped Classical in

inductive ResolventDatum (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] : Type 1

  | s3 (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
      (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (θ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
      (hL : Module.finrank ℚ L = 2)
      (hω : IsFiniteOrderHeckeChar ℚ ω) (hθ : IsFiniteOrderHeckeChar L θ)
      (eulerω : ∀ p : HeightOneSpectrum (𝓞 ℚ), zetaEulerPoly L p =
        (Polynomial.C 1 - Polynomial.X) * (Polynomial.C 1 - Polynomial.C (eulerCoeff ℚ ω p) * Polynomial.X))
      (eulerθ : ∀ p : HeightOneSpectrum (𝓞 ℚ), zetaEulerPoly K p =
        (Polynomial.C 1 - Polynomial.X) * inducedEulerPoly ℚ (eulerCoeff L θ) p)
      (archω : ∀ w : InfinitePlace ℚ, IsArchCompAt ℚ ω w 0 ((resolventSignBit L).val : ℤ))
      (archθR : ∀ u : InfinitePlace L, u.IsReal → IsArchCompAt L θ u 0 (((0 : ZMod 2)).val : ℤ))
      (archθC : ∀ u : InfinitePlace L, u.IsComplex → IsArchCompAt L θ u 0 0)
      (sig : nrRealPlaces K = nrRealPlaces L + 1 ∧ nrComplexPlaces K = nrComplexPlaces L) :
      ResolventDatum K

  | cyclic (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsFiniteOrderHeckeChar ℚ χ)
      (eulerχ : ∀ p : HeightOneSpectrum (𝓞 ℚ), zetaEulerPoly K p =
        (Polynomial.C 1 - Polynomial.X) * (Polynomial.C 1 - Polynomial.C (eulerCoeff ℚ χ p) * Polynomial.X) *
          (Polynomial.C 1 - Polynomial.C (eulerCoeff ℚ (χ ^ 2) p) * Polynomial.X))
      (archχ : ∀ w : InfinitePlace ℚ, IsArchCompAt ℚ χ w 0 (((0 : ZMod 2)).val : ℤ))
      (sig : nrComplexPlaces K = 0) :
      ResolventDatum K

end LanglandsTunnell.CubicLambda
