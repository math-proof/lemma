import Lemma.LanglandsTunnell.StandardLocalConstantsAt
import Lemma.LanglandsTunnell.ArchEpsilon
import Lemma.LanglandsTunnell.HonestLDatum
import Lemma.NumberField.TateGlobalZeta
import Lemma.AutomorphicForm.HeckeEigenfunction
import Def.LanglandsTunnell_ConverseData

set_option autoImplicit false


noncomputable section

open NumberField AutomorphicForm IsDedekindDomain LanglandsTunnell
open NumberField.TateGlobal

namespace LanglandsTunnell.Converse

variable (K : Type) [Field K] [NumberField K]

theorem sPartDual_const_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Ad : (↥S → ℤ) → ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s c : ℂ) :
    c * sPartDual K S Ad μ s = sPartDual K S (fun n => c * Ad n) μ s := by
  unfold sPartDual
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

theorem sPart_empty (A : (↥(∅ : Finset (HeightOneSpectrum (𝓞 K))) → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (n₀ : ↥(∅ : Finset (HeightOneSpectrum (𝓞 K))) → ℤ) :
    sPart K ∅ A μ s = A n₀ := by
  haveI : IsEmpty ↥(∅ : Finset (HeightOneSpectrum (𝓞 K))) := ⟨fun v => Finset.notMem_empty v.1 v.2⟩
  have hsub : ∀ n : ↥(∅ : Finset (HeightOneSpectrum (𝓞 K))) → ℤ, n = n₀ :=
    fun n => funext fun v => isEmptyElim v
  unfold sPart
  rw [tsum_eq_single n₀ (fun n hn => (hn (hsub n)).elim), Fintype.prod_empty, mul_one]

end LanglandsTunnell.Converse

end
