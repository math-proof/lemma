import Lemma.Definitions.Def_LanglandsTunnell_ConverseData

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

def sWeight (S : Finset (HeightOneSpectrum (𝓞 K))) (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (α : Kˣ) (s : ℂ) : ℂ :=
  ∏ v : ↥S,
    ((localChar χ v.1 (localOf K v.1 α) : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
        (((WithZero.log (Valued.v (((localOf K v.1 α : (v.1.adicCompletion K)ˣ)) : v.1.adicCompletion K)) : ℤ) : ℂ)
          * (s - 1 / 2))

def IsJLTwist (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop :=
  IsAdmissibleTwist K μ ∧
    ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      localChar μ v u * epsS v u = 1

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

def sSum (d : JLData K S epsS ω) (R : SOrderReps K S) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∑' n : ↥S → ℤ, d.a (R.rep n) * sWeight K S μ (R.rep n) s

def sSumDual (d : JLData K S epsS ω) (R : SOrderReps K S) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∑' n : ↥S → ℤ, d.ad (R.rep n) * sWeight K S (ω * μ)⁻¹ (R.rep n) s

def sFactor (d : JLData K S epsS ω) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∏ v : ↥S,
    ((localChar μ v.1 (localOf K v.1 (-d.A)) : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((d.m v : ℕ) : ℂ) * (s - 1 / 2))

end JLData

variable (K)

def IsJLNice (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (d : JLData K S epsS ω)
    (Pi : HeckeEigensystem K ℂ)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam) : Prop :=
  ∃ R : SOrderReps K S, ∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsJLTwist K S epsS μ →
    ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
      (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
      (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
      (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
      let D := twistedDatum K Pi S archR archC μ uR aR uC kC
      D.WellFormed ∧ D.Converges ∧
      ∃ σ₀ : ℝ, ∃ Λ Λd : ℂ → ℂ,
        Differentiable ℂ Λ ∧ Differentiable ℂ Λd ∧
        LDatum.BoundedOnStrips Λ ∧ LDatum.BoundedOnStrips Λd ∧
        (∀ s : ℂ, σ₀ < s.re →
          Summable (fun n : ↥S → ℤ => d.a (R.rep n) * sWeight K S μ (R.rep n) s) ∧
          Summable (fun n : ↥S → ℤ => d.ad (R.rep n) * sWeight K S (ω * μ)⁻¹ (R.rep n) s) ∧
          Λ s = d.sSum R μ s * D.archFactor s * D.LFun s ∧
          Λd s = d.sSumDual R μ s * D.archFactorDual s * D.LFunDual s) ∧
        (∀ s : ℂ,
          Λ s = d.sFactor μ s * pinnedRootNumber K Pi μ S archR archC uR aR uC kC *
            ((finiteConductor K μ S : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * Λd (1 - s))

example {v : HeightOneSpectrum (𝓞 K)} (ψ : AddChar (v.adicCompletion K) ℂ) :
    addCharLevel ψ = sSup {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1} :=
  addCharLevel_def ψ

end LanglandsTunnell.Converse

end
