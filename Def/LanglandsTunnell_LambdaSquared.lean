import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Discriminant
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell.CubicInduction

def IsAnisotropicAt (a b : ℚ) (p : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  ¬ ∃ z x y : p.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
    z ^ 2 - algebraMap ℚ (p.adicCompletion ℚ) a * x ^ 2
      - algebraMap ℚ (p.adicCompletion ℚ) b * y ^ 2 = 0

variable (K : Type) [Field K] [NumberField K]

noncomputable def discQ : ℚ := Algebra.discr ℚ (Module.finBasis ℚ K)


open scoped Classical in

noncomputable def lamSq (p : HeightOneSpectrum (𝓞 ℚ)) : ℂ :=
  if IsAnisotropicAt (discQ K) (-1) p then -1 else 1

noncomputable def lamSqArch : ℂ := if discQ K < 0 then -1 else 1


section PlacesOfK

variable [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

noncomputable def lamSqFin (w : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal = 1 ∧
      (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal = 1 then 1
  else lamSq K (w.under (𝓞 ℚ))

end PlacesOfK

end LanglandsTunnell.CubicInduction
