import Lemma.AutomorphicForm.TwistedOrbital
import Def.AutomorphicForm_FormalBaseChange
import Lemma.NumberField.PrincipalLevel
import Lemma.NumberField.TateGlobalZeta
import Lemma.LanglandsTunnell.ConverseData
import Lemma.LocalLanglands.HeckeCosetLocal
import Lemma.M4aHerbrand.GenuineDescent
import Lemma.TwistedNormClasses.Main
import Lemma.AdelicDock.LocalEmbedding
import Lemma.AutomorphicForm.GL2ConjugacyCells
import Lemma.AutomorphicForm.TruncationOperator
import Lemma.AutomorphicForm.TwistedAdelicKernel
import Def.NumberField_AdelicHeight
import Lemma.Analysis.HalfLineIntercept

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

def AutomorphicForm.twistedGeometricRemainder
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ΦL Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) : ℂ :=
  HalfLine.intercept (fun R : ℝ =>
    (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (@AutomorphicForm.lambdaT _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y)
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
    (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L)))

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.twistedGeometricRemainder_eq_of_forall_le_setIntegral_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (μ ν : (HeightOneSpectrum (𝓞 K) → ℕ) → (HeightOneSpectrum (𝓞 K) → ℕ) → ℂ) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T S → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      (∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → (
  ∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (@AutomorphicForm.lambdaT _
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
        (fun t => AutomorphicForm.unipotentGL2 t)
        (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
        (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y)
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
    ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
  (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
        φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
    ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) +
      ((R : ℂ) * ν ks js + μ ks js)) →
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      AutomorphicForm.twistedGeometricRemainder K L D σ hgen ΦL Φ₀ νZL ΩL ξL φ = μ ks js := by
  intro T _ _ _ ws w' _ ϖs _ hϖs0 ns rTs _ zs _ hspan ks js φ φf hfac
  obtain ⟨R₀, hR⟩ := hspan ks js φ φf hfac
  unfold AutomorphicForm.twistedGeometricRemainder
  exact HalfLine.intercept_eq_of_forall_le_eq_add_mul ⟨R₀, fun R hle => sub_eq_iff_eq_add'.mpr (hR R hle)⟩

open AutomorphicForm in
open scoped TensorProduct.RightActions in

example
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (_hα : 0 < α)  (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (_hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (_hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (_SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (_hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (_hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (_S : Finset (HeightOneSpectrum (𝓞 K)))
    (_φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (_φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (c u d₁ d₂ : ℝ) (_hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (_hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (_hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (_hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (_hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) : ℂ :=
  AutomorphicForm.twistedGeometricRemainder K L D σ hgen ΦL Φ₀ νZL ΩL ξL φ

end
