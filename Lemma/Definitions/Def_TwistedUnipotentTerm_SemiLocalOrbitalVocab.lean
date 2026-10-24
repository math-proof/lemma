import Lemma.Definitions.Def_AdelicDock_LocalEmbedding
import Lemma.Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Lemma.Definitions.Def_NumberField_TateGlobalZeta

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace TwistedUnipotentTerm

section Definitions

noncomputable def semiLocalUnipotent
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : L ⊗[K] v.adicCompletion K) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

noncomputable def semiLocalCentral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
  Units.map (Matrix.scalar (Fin 2) : L ⊗[K] v.adicCompletion K →+* Matrix (Fin 2) (Fin 2) _).toMonoidHom ζ

noncomputable def semiLocalUnitComponent (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (ζ : (L ⊗[K] v.adicCompletion K)ˣ) : (w.1.adicCompletion L)ˣ :=
  Units.map (Pi.evalMonoidHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w)
    (Units.mapEquiv (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toRingEquiv.toMulEquiv ζ)

noncomputable def semiLocalCharacter (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ζ : (L ⊗[K] v.adicCompletion K)ˣ) : ℂ :=
  ∏ᶠ w : v.Extension (𝓞 L),
    ((ξL ⟨Matrix.GeneralLinearGroup.det
        (NumberField.AdelicLevel.heckeGenAt (𝓞 L) L w.1 (semiLocalUnitComponent K L v w ζ)),
      Subgroup.mem_top _⟩ : ℂˣ) : ℂ)

noncomputable def wordIndicator (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) (m : ℕ)
    (rT : Fin m → GL (Fin 2) (w.1.adicCompletion L)) (z : GL (Fin 2) (w.1.adicCompletion L)) (k j : ℕ)
    (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : ℂ :=
  ∑ ι : Fin k → Fin m,
    (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
      ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1
        ((List.ofFn fun i => rT (ι i)).prod * z ^ j)))⁻¹ * x)

open scoped TensorProduct.RightActions in

noncomputable def unipotentOrbitalFn (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : v.Extension (𝓞 L)) (m : ℕ) (rT : Fin m → GL (Fin 2) (w.1.adicCompletion L))
    (z : GL (Fin 2) (w.1.adicCompletion L)) (k j : ℕ) (x : L ⊗[K] v.adicCompletion K) : ℂ :=
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (v.adicCompletion K)
  haveI : LocallyCompactSpace (L ⊗[K] v.adicCompletion K)ˣ :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  letI : MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ := borel _
  haveI : BorelSpace (L ⊗[K] v.adicCompletion K)ˣ := ⟨rfl⟩
  ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
    semiLocalCharacter K L ξL v ζ *
      ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
        wordIndicator K L v w m rT z k j (κ⁻¹ * semiLocalCentral K L v ζ * semiLocalUnipotent K L v x)
          ∂(AutomorphicForm.semiLocalHaar K L v)
    ∂(Measure.haar : Measure (L ⊗[K] v.adicCompletion K)ˣ)

end Definitions

end TwistedUnipotentTerm

section RootDefinitions

open AutomorphicForm in

noncomputable def twistedLocalFactor
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (m : ℕ) (rT : Fin m → GL (Fin 2) (w.1.adicCompletion L)) (z : GL (Fin 2) (w.1.adicCompletion L)) (k j : ℕ) :
    v.adicCompletion K → ℂ :=
  have _ := D
  have _ := σ
  letI : MeasurableSpace (v.adicCompletion K) := borel _
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  AdelicTracePushforward.localTracePushforward K L v (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w m rT z k j)

def IsJointFactorizableStandardOutside {F : Type} [Field F] [NumberField F] (f : AdeleRing (𝓞 F) F → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (g : InfiniteAdeleRing F → ℂ)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) : Prop :=
  ∀ x, f x = (NumberField.TateGlobal.integralOutside S).indicator
    (fun x => g x.1 * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x

end RootDefinitions

end
