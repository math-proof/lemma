import Lemma.Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Lemma.Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace AutomorphicForm

section TierRefined

variable (K : Type) [Field K] [NumberField K]

def IsUnitFactorizableOfTypeAt (tys : ArchTypeFamily K)
    (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  IsUnitFactorizableAt K U S f ∧ IsArchBiFinite K tys f

variable {K}

theorem IsUnitFactorizableOfTypeAt.isUnitFactorizableAt {tys : ArchTypeFamily K}
    {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableOfTypeAt K tys U S f) :
    IsUnitFactorizableAt K U S f :=
  hf.1

theorem IsUnitFactorizableOfTypeAt.isArchBiFinite {tys : ArchTypeFamily K}
    {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableOfTypeAt K tys U S f) :
    IsArchBiFinite K tys f :=
  hf.2

theorem IsUnitFactorizableOfTypeAt.isFactorizableTestFn {tys : ArchTypeFamily K}
    {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableOfTypeAt K tys U S f) :
    IsFactorizableTestFn K f :=
  hf.1.isFactorizableTestFn K

theorem IsUnitFactorizableOfTypeAt.mono {tys : ArchTypeFamily K}
    {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hUV : U ≤ V)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableOfTypeAt K tys V S f) : IsUnitFactorizableOfTypeAt K tys U S f :=
  ⟨hf.1.mono K hUV, hf.2⟩

theorem IsUnitFactorizableOfTypeAt.mono_type {tys tys' : ArchTypeFamily K}
    (h : tys.IsContainedIn K tys') {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableOfTypeAt K tys U S f) : IsUnitFactorizableOfTypeAt K tys' U S f :=
  ⟨hf.1, hf.2.mono K h⟩

theorem IsUnitFactorizableAt.isUnitFactorizableOfTypeAt_of_factorization {tys : ArchTypeFamily K}
    {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableAt K U S f)
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    (hfac : ∀ g, f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))
    (hfa : IsArchFactorBiFinite K tys fa) : IsUnitFactorizableOfTypeAt K tys U S f :=
  ⟨hf, IsArchBiFinite.of_factorization K hfac hfa⟩

variable (K)

theorem isUnitFactorizableOfTypeAt_zero (tys : ArchTypeFamily K)
    (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsUnitFactorizableOfTypeAt K tys U S fun _ => 0 :=
  ⟨isUnitFactorizableAt_zero K U S, isArchBiFinite_zero K tys⟩

theorem isUnitFactorizableOfTypeAt_mul_indicator_unitFinSet (tys : ArchTypeFamily K)
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (hfa : IsArchTestFactor K fa)
    (hfa' : IsArchFactorBiFinite K tys fa) {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    (hU : IsIntegralLevel K U) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsUnitFactorizableOfTypeAt K tys U S fun g => fa (AdelicLevel.glArch (𝓞 K) K g) *
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 K) K g) :=
  (isUnitFactorizableAt_mul_indicator_unitFinSet K hfa hU S).isUnitFactorizableOfTypeAt_of_factorization
    (fun _ => rfl) hfa'

end TierRefined

end AutomorphicForm
