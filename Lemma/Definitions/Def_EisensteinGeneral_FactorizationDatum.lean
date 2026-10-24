import Lemma.Definitions.Def_AutomorphicForm_WeylIntertwining
import Lemma.Definitions.Def_NumberField_TateGlobalZeta
import Lemma.Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

namespace EisensteinGeneral.Piece

open scoped Classical in

structure FactorizationDatum (F : Type) [Field F] [NumberField F]
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
    (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) where
  cS : HeightOneSpectrum (𝓞 F) → ℕ
  mS : ℕ
  n : ℕ
  A : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ
  B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ
  h : Fin n → (v : HeightOneSpectrum (𝓞 F)) → ℂ → v.adicCompletion F → ℂ
  kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ
  τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ
  abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ
  τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ
  Wr : Fin n → {w : InfinitePlace F // w.IsReal} → ℂ → ℝ → ℂ
  Wc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ → ℂ
  a : (AdeleRing (𝓞 F) F)ˣ
  u : AdeleRing (𝓞 F) F
  C : Fin n → ℂ → ℂ
  hχϖ : ∀ v, ‖((NumberField.TateGlobal.localChar χ v (ϖ v) : ℂˣ) : ℂ)‖ = 1
  hχS : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      NumberField.TateGlobal.localChar χ v u = 1
  hnψ : ∀ v ∉ S, nψ v = 0
  hcS : ∀ v ∈ S, 1 ≤ cS v
  hχc : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (cS v),
      NumberField.TateGlobal.localChar χ v u = 1
  hmS : 1 ≤ mS
  hA : ∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → A j v y = A j v x
  hB : ∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → B j v y = B j v x
  hoff : ∀ (j : Fin n), ∀ v ∉ S, ∀ (s : ℂ) (x : v.adicCompletion F),
      h j v s x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x
  hon : ∀ (j : Fin n), ∀ v ∈ S, ∀ (s : ℂ) (x : v.adicCompletion F),
      h j v s x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B j v y⁻¹) x
  habm : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2
  hWr : ∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}) (s : ℂ) (x : ℝ),
      Wr j i s x = ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ (kdat j i)
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2))
  hWc : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) (s z : ℂ),
      Wc j w s z = z ^ (abm j w).1 * (starRingEnd ℂ) z ^ (abm j w).2.1
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2))
  hC : ∀ j, Differentiable ℂ (C j)
  hfac : ∀ (s : ℂ) (y : AdeleRing (𝓞 F) F),
      Ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)
        = ∑ j : Fin n, C j s
          * (∏ i : {w : InfinitePlace F // w.IsReal},
              Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).1 i))
          * (∏ w : {w : InfinitePlace F // w.IsComplex},
              Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), h j v s ((a • (y + u)).2 v)

end EisensteinGeneral.Piece
