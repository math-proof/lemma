import Instance.TaylorWiles_Primes
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Fixed

set_option autoImplicit false

open scoped NNReal
open Filter Topology Asymptotics

namespace FrobeniusDensity

open NumberField Ideal

section DegOneCount

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in

noncomputable def degOneCount (ℓ : ℕ) : ℕ :=
  if ℓ.Prime then
    {𝔮 ∈ (ratPrimeIdeal ℓ).primesOver (𝓞 K) | Nat.card ((𝓞 K) ⧸ 𝔮) = ℓ}.ncard
  else 0

end DegOneCount

section AnalyticInput

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]

def DegOneAsymptotic : Prop :=
  ∀ (H : Subgroup (L ≃ₐ[ℚ] L)) (S₀ : Finset ℕ),
    (∀ s : ℝ, 1 < s → Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
        (degOneCount (FixedPoints.intermediateField H : IntermediateField ℚ L) ℓ : ℝ))
      * (ℓ : ℝ) ^ (-s))) ∧
    (fun s : ℝ => (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
        (degOneCount (FixedPoints.intermediateField H : IntermediateField ℚ L) ℓ : ℝ))
      * (ℓ : ℝ) ^ (-s)) + Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ))

end AnalyticInput

end FrobeniusDensity
