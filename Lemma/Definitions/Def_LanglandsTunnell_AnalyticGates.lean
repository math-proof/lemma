import Lemma.Definitions.Def_LanglandsTunnell_TowerCounting
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField FrobeniusDensity Filter Topology Asymptotics

def OrderEightNonvanishing (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] : Prop :=
  ∀ (σ : L ≃ₐ[ℚ] L), orderOf σ = 8 →
  ∀ (S₀ : Finset ℕ) (ζ : ℂ), IsPrimitiveRoot ζ 8 →
  ∀ j ∈ oddJ, (fun s : ℝ => ∑' ℓ : ℕ,
    (∑ m : Fin 8, (labelledCount σ S₀ m ℓ : ℂ) * ζ ^ (j * m.val)) *
    (↑((ℓ : ℝ) ^ (-s)) : ℂ)) =o[𝓝[>] 1] (fun s : ℝ => Real.log ((s - 1)⁻¹))

def OrderEightBounded (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] : Prop :=
  ∀ (σ : L ≃ₐ[ℚ] L), orderOf σ = 8 →
  ∀ (S₀ : Finset ℕ) (ζ : ℂ), IsPrimitiveRoot ζ 8 →
  ∀ j ∈ oddJ, (fun s : ℝ => ∑' ℓ : ℕ,
    (∑ m : Fin 8, (labelledCount σ S₀ m ℓ : ℂ) * ζ ^ (j * m.val)) *
    (↑((ℓ : ℝ) ^ (-s)) : ℂ)) =O[𝓝[>] 1] (fun _ => (1 : ℝ))

def TauberianHypothesis (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] : Prop :=
  ∀ (σ : L ≃ₐ[ℚ] L) (c : ℝ),
    ((∀ s : ℝ, 1 < s → Summable (fun ℓ : ℕ => (classIndicator σ ℓ : ℝ) * (ℓ : ℝ) ^ (-s))) ∧
     (fun s : ℝ => (∑' ℓ : ℕ, (classIndicator σ ℓ : ℝ) * (ℓ : ℝ) ^ (-s))
       + c * Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)))
    → Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter (fun ℓ => classIndicator σ ℓ = 1)).card : ℝ)
          / (((Finset.range N).filter Nat.Prime).card : ℝ))
        atTop (𝓝 c)

end LanglandsTunnell
