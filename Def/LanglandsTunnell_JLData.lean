import Lemma.LanglandsTunnell.ConverseData
import Structure.LanglandsTunnell_JLData

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.TateGlobal LanglandsTunnell.TateLocal NumberField.StandardAddChar
noncomputable section

namespace LanglandsTunnell.Converse

variable (K : Type) [Field K] [NumberField K]


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
