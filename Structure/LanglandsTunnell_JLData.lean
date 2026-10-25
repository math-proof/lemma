import Def.LanglandsTunnell_ConverseData

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.TateGlobal LanglandsTunnell.TateLocal NumberField.StandardAddChar
noncomputable section

namespace LanglandsTunnell.Converse

variable (K : Type) [Field K] [NumberField K]

def localOf (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) : (v.adicCompletion K)ˣ :=
  Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom α

def IsOneMod (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (u : (v.adicCompletion K)ˣ) : Prop :=
  Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ))

def IsSUnit (S : Finset (HeightOneSpectrum (𝓞 K))) (β : Kˣ) : Prop :=
  ∀ v : ↥S, Valued.v ((localOf K v.1 β : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) = 1


structure JLData (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) where

  m : ↥S → ℕ
  m_pos : ∀ v, 1 ≤ m v

  epsS_level : ∀ (v : ↥S) (u : (v.1.adicCompletion K)ˣ), Valued.v (u : v.1.adicCompletion K) = 1 →
    IsOneMod K v.1 (m v) u → epsS v.1 u = 1

  central_level : ∀ (v : ↥S) (u : (v.1.adicCompletion K)ˣ), Valued.v (u : v.1.adicCompletion K) = 1 →
    IsOneMod K v.1 (m v) u → localChar ω v.1 u = 1

  A : Kˣ
  A_ord : ∀ v : ↥S, Valued.v ((localOf K v.1 A : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
    = WithZero.exp (-(m v : ℤ))

  a : Kˣ → ℂ
  ad : Kˣ → ℂ

  bounded : ∃ C : ℝ, ∀ α, ‖a α‖ ≤ C ∧ ‖ad α‖ ≤ C

  a_mul : ∀ α β : Kˣ, IsSUnit K S β →
    a (α * β) = (∏ v : ↥S, ((epsS v.1 (localOf K v.1 β) : ℂˣ) : ℂ)) * a α

  ad_mul : ∀ α β : Kˣ, IsSUnit K S β →
    ad (α * β) =
      (∏ v : ↥S, ((localChar ω v.1 (localOf K v.1 β) : ℂˣ) : ℂ) * (((epsS v.1 (localOf K v.1 β))⁻¹ : ℂˣ) : ℂ))
        * ad α

  floor : ∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v (((localOf K v.1 α : (v.1.adicCompletion K)ˣ)) : v.1.adicCompletion K)
      ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) → a α = 0 ∧ ad α = 0

  a_ne_zero : ∃ α, a α ≠ 0

structure SOrderReps (S : Finset (HeightOneSpectrum (𝓞 K))) where
  rep : (↥S → ℤ) → Kˣ
  rep_ord : ∀ (n : ↥S → ℤ) (v : ↥S),
    Valued.v ((localOf K v.1 (rep n) : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) = WithZero.exp (-(n v))

variable {K}

namespace JLData

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
  {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}


end JLData

variable (K)


end LanglandsTunnell.Converse

end
