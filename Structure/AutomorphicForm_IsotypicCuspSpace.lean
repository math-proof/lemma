import Lemma.AutomorphicForm.ProductionPinsGeneral
import Def.AutomorphicForm_RightConvolution
import Def.AutomorphicForm_SigmaAdelicAction
import Lemma.AutomorphicForm.ArchWeightChar

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

section Isotypic

variable (K : Type) [Field K] [NumberField K]

structure IsIsotypicCuspFormAt (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) : Prop where
  smoothCusp : IsSmoothCuspAutomorphicFnAt K pins ξ φ
  continuous : Continuous φ
  level_invariant : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ pins.U N, φ (g * u) = φ g
  hecke_eigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    SmoothCusp.IsHeckeCosetEigenfunctionAt K (pins.U N) (pins.gen v) v φ (Φ.a v)
  central_eigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
    φ (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (pins.gen v)) * g)
      = Φ.toRawCentral.b v * φ g


variable {K}


variable (K)


variable {K}


end Isotypic

section Classes

variable (K : Type) [Field K] [NumberField K]


variable {K}


end Classes

section Trace

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

structure IsStableLinearOn (V : Submodule ℂ M) (T : M → M) : Prop where
  mapsTo : ∀ u ∈ V, T u ∈ V
  map_add : ∀ u ∈ V, ∀ w ∈ V, T (u + w) = T u + T w
  map_smul : ∀ (c : ℂ) (u : M), u ∈ V → T (c • u) = c • T u


end Trace

section Operators

variable (K : Type) [Field K] [NumberField K]


open Classical in


variable (F L : Type) [Field F] [Field L] [NumberField L] [Algebra F L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) F L)


open Classical in


end Operators

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]


end TypePiece

section ArchCut

variable (F : Type) [Field F] [NumberField F]

structure ArchRepAt (w : InfinitePlace F) where

  n : ℕ

  ρ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin n → ℂ)


structure ArchTypeFamily where

  card : InfinitePlace F → ℕ

  rep : (w : InfinitePlace F) → Fin (card w) → ArchRepAt F w


end ArchCut

section ArchFactor

variable (F : Type) [Field F] [NumberField F]


end ArchFactor

section CutTrace

variable (K : Type) [Field K] [NumberField K]


variable (F L : Type) [Field F] [Field L] [NumberField L] [Algebra F L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) F L)


end CutTrace

end AutomorphicForm

end
