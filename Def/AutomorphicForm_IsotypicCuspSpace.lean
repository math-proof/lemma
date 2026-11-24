module
public import Def.AutomorphicForm_ProductionPinsGeneral
public import Theorem.Matrix.RightConvolution
public import Theorem.Matrix.SigmaAdelicAction
public import Def.AutomorphicForm_ArchWeightChar
public import Structure.AutomorphicForm_IsotypicCuspSpace
set_option autoImplicit false
open IsDedekindDomain NumberField


public section

noncomputable section

namespace AutomorphicForm

section Isotypic

variable (K : Type) [Field K] [NumberField K]


def isotypicCuspSubmodule (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ) :
    Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
  Submodule.span ℂ {φ | IsIsotypicCuspFormAt K pins ξ N S Φ φ}

variable {K}

variable (K)

variable {K}

def IsIsotypicCuspFormAt.toRealization {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ : HeckeEigensystem K ℂ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : IsIsotypicCuspFormAt K pins ξ Φ.level S Φ φ)
    (h0 : φ ≠ 0) : SmoothCuspRealizationAt K pins Φ.toRawCentral where
  toFun := φ
  exists_ne_zero := Function.ne_iff.mp h0
  centralChar := ξ
  smoothCusp := h.smoothCusp
  level_invariant := h.level_invariant
  exceptionalSet := S
  hecke_eigen := h.hecke_eigen
  central_eigen := h.central_eigen

end Isotypic

section Classes

variable (K : Type) [Field K] [NumberField K]

def cuspClasses (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (HeckeEigensystem K ℂ) :=
  {Φ | Φ.level = N ∧ (∀ v ∈ S, Φ.a v = 0 ∧ Φ.b v = 0) ∧
    isotypicCuspSubmodule K pins ξ N S Φ ≠ ⊥}

variable {K}

end Classes

section Trace

variable {M : Type*} [AddCommGroup M] [Module ℂ M]


def IsStableLinearOn.toEnd {V : Submodule ℂ M} {T : M → M} (h : IsStableLinearOn V T) :
    V →ₗ[ℂ] V where
  toFun u := ⟨T u, h.mapsTo u u.2⟩
  map_add' u w := Subtype.ext (h.map_add u u.2 w w.2)
  map_smul' c u := Subtype.ext (h.map_smul c u u.2)

def traceOn (V : Submodule ℂ M) (T : M → M) (h : IsStableLinearOn V T) : ℂ :=
  LinearMap.trace ℂ V h.toEnd

end Trace

section Operators

variable (K : Type) [Field K] [NumberField K]

def convOp (f : AdelicGL2 (𝓞 K) K → ℂ) :
    (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
  fun u => rightConv K u f

open Classical in

def convTraceOn (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) (hV : ∀ u ∈ V, Continuous u)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) : ℂ :=
  if hmaps : ∀ u ∈ V, convOp K f u ∈ V then
    traceOn V (convOp K f) (isStableLinearOn_convOp K hV hf hfc hmaps) else 0

variable (F L : Type) [Field F] [Field L] [NumberField L] [Algebra F L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) F L)

def twistedConvOp (σ : L ≃ₐ[F] L) (f : AdelicGL2 (𝓞 L) L → ℂ) :
    (AdelicGL2 (𝓞 L) L → ℂ) → (AdelicGL2 (𝓞 L) L → ℂ) :=
  fun u => rightConv L (sigmaSectionActOn F L D σ u) f

open Classical in

def twistedConvTraceOn (σ : L ≃ₐ[F] L) (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : ∀ u ∈ V, Continuous u) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) : ℂ :=
  if hmaps : ∀ u ∈ V, twistedConvOp F L D σ f u ∈ V then
    traceOn V (twistedConvOp F L D σ f) (isStableLinearOn_twistedConvOp F L D σ hV hf hfc hmaps)
  else 0

end Operators

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def IsRightEquivariant (ι : H →* G) (ρ : Representation ℂ H W) (T : W →ₗ[ℂ] (G → ℂ)) :
    Prop :=
  ∀ (k : H) (v : W) (x : G), T (ρ k v) x = T v (x * ι k)

def typeSubmodule (ι : H →* G) (ρ : Representation ℂ H W) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ
    {f | ∃ T : W →ₗ[ℂ] (G → ℂ), IsRightEquivariant ι ρ T ∧ f ∈ LinearMap.range T}

def charRep (χ : H →* ℂˣ) : Representation ℂ H (Fin 1 → ℂ) :=
  (DistribMulAction.toModuleEnd ℂ (Fin 1 → ℂ)).comp ((Units.coeHom ℂ).comp χ)

end TypePiece

section ArchCut

variable (F : Type) [Field F] [NumberField F]


def ArchRepAt.ofChar {w : InfinitePlace F} (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ) :
    ArchRepAt F w where
  n := 1
  ρ := charRep χ

def rowIsometryInclAt₀ (w : InfinitePlace F) :
    rowIsometrySubgroup₀ w.Completion →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLInclAt F w).comp (rowIsometrySubgroup₀ w.Completion).subtype

def archRowIsometrySubgroup₀ (w : InfinitePlace F) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (rowIsometrySubgroup₀ w.Completion).map (adelicArchGLInclAt F w)

def archTypeSubmoduleAt (w : InfinitePlace F) (τ : ArchRepAt F w) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  typeSubmodule (rowIsometryInclAt₀ F w) τ.ρ

def archDualTypeSubmoduleAt (w : InfinitePlace F) (τ : ArchRepAt F w) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  typeSubmodule (rowIsometryInclAt₀ F w) τ.ρ.dual


def ArchTypeFamily.ofChar (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ) :
    ArchTypeFamily F where
  card := fun _ => 1
  rep := fun w _ => ArchRepAt.ofChar F (χ w)

def archCutSubmodule (tys : ArchTypeFamily F) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  ⨅ w : InfinitePlace F, ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)

def archDualCutSubmodule (tys : ArchTypeFamily F) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  ⨅ w : InfinitePlace F, ⨆ i : Fin (tys.card w), archDualTypeSubmoduleAt F w (tys.rep w i)

def ArchTypeFamily.IsContainedIn (tys tys' : ArchTypeFamily F) : Prop :=
  ∀ (w : InfinitePlace F) (i : Fin (tys.card w)),
    ∃ j : Fin (tys'.card w), tys'.rep w j = tys.rep w i

def IsArchBiFinite (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  (fun x => f x⁻¹) ∈ archCutSubmodule F tys ∧ f ∈ archDualCutSubmodule F tys

end ArchCut

section ArchFactor

variable (F : Type) [Field F] [NumberField F]

def archRowIsometryInclAt₀ (w : InfinitePlace F) :
    rowIsometrySubgroup₀ w.Completion →* GL (Fin 2) (InfiniteAdeleRing F) :=
  (archGLIncl F w).comp (rowIsometrySubgroup₀ w.Completion).subtype

def archFactorTypeSubmoduleAt (w : InfinitePlace F) (τ : ArchRepAt F w) :
    Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
  typeSubmodule (archRowIsometryInclAt₀ F w) τ.ρ

def archFactorDualTypeSubmoduleAt (w : InfinitePlace F) (τ : ArchRepAt F w) :
    Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
  typeSubmodule (archRowIsometryInclAt₀ F w) τ.ρ.dual

def archFactorCutSubmodule (tys : ArchTypeFamily F) :
    Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
  ⨅ w : InfinitePlace F, ⨆ i : Fin (tys.card w), archFactorTypeSubmoduleAt F w (tys.rep w i)

def archFactorDualCutSubmodule (tys : ArchTypeFamily F) :
    Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
  ⨅ w : InfinitePlace F, ⨆ i : Fin (tys.card w), archFactorDualTypeSubmoduleAt F w (tys.rep w i)

def IsArchFactorBiFinite (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    Prop :=
  (fun x => fa x⁻¹) ∈ archFactorCutSubmodule F tys ∧ fa ∈ archFactorDualCutSubmodule F tys

omit [NumberField F] in

end ArchFactor

section CutTrace

variable (K : Type) [Field K] [NumberField K]

def cutTrace (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) (tys : ArchTypeFamily K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) : ℂ :=
  convTraceOn K (isotypicCuspSubmodule K pins ξ N S Ψ ⊓ archCutSubmodule K tys)
    (continuous_of_mem_isotypicCuspSubmodule_inf K) f hf hfc

variable (F L : Type) [Field F] [Field L] [NumberField L] [Algebra F L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) F L)

def twistedCutTrace (σ : L ≃ₐ[F] L) (pins : CarrierPins L) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 L))
    (S : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ) (tys : ArchTypeFamily L)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) : ℂ :=
  twistedConvTraceOn F L D σ (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ archCutSubmodule L tys)
    (continuous_of_mem_isotypicCuspSubmodule_inf L) f hf hfc

end CutTrace

end AutomorphicForm

end
