import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Lemma.Definitions.Def_AlgebraicCurve_DivisorPushPull
import Lemma.Definitions.Def_ModularCurve_CanonicalDivisor
import Lemma.Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Lemma.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Lemma.Definitions.Def_AlgebraicCurve_AdelicIndex
import Lemma.Definitions.Def_AlgebraicCurve_LocalResidue
import Lemma.Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Lemma.Definitions.Def_AlgebraicCurve_PlaceCompletion

set_option autoImplicit false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open LinearMap Submodule

noncomputable section

namespace ModularCurve.KwF4gRRTate

section FinrankTrace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def finrankTrace (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] : K :=
  LinearMap.trace K (LinearMap.range φ)
    (φ.restrict (fun x _ => LinearMap.mem_range_self φ x))

end FinrankTrace

section TateComm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def tateComm (pA φ ψ : V →ₗ[K] V) : V →ₗ[K] V :=
  pA ∘ₗ φ ∘ₗ pA ∘ₗ ψ - pA ∘ₗ ψ ∘ₗ pA ∘ₗ φ

theorem tateComm_apply (pA φ ψ : V →ₗ[K] V) (x : V) :
    tateComm pA φ ψ x = pA (φ (pA (ψ x))) - pA (ψ (pA (φ x))) := rfl

theorem tateComm_mem_range (pA φ ψ : V →ₗ[K] V) (x : V) :
    tateComm pA φ ψ x ∈ LinearMap.range pA :=
  sub_mem (LinearMap.mem_range_self pA _) (LinearMap.mem_range_self pA _)

theorem tateComm_antisymm (pA φ ψ : V →ₗ[K] V) :
    tateComm pA φ ψ = - tateComm pA ψ φ := by
  unfold tateComm; rw [neg_sub]

def tateCommRestrict (pA φ ψ : V →ₗ[K] V) :
    LinearMap.range pA →ₗ[K] LinearMap.range pA :=
  (tateComm pA φ ψ).restrict (fun x _ => tateComm_mem_range pA φ ψ x)

theorem tateCommRestrict_apply (pA φ ψ : V →ₗ[K] V) (a : LinearMap.range pA) :
    (tateCommRestrict pA φ ψ a : V) = tateComm pA φ ψ (a : V) := rfl

def tateCommTrace (pA φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ ψ))] : K :=
  finrankTrace (tateCommRestrict pA φ ψ)

end TateComm

section TateFactoring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem tateComm_eq_of_commute {pA φ ψ : V →ₗ[K] V}
    (hcomm : φ ∘ₗ ψ = ψ ∘ₗ φ) (a : V) :
    tateComm pA φ ψ a
      = pA (ψ (φ a - pA (φ a))) - pA (φ (ψ a - pA (ψ a))) := by
  have hφψ : φ (ψ a) = ψ (φ a) := by
    have := congrArg (fun f => f a) (congrArg DFunLike.coe hcomm)
    simpa using this
  rw [tateComm_apply, map_sub, map_sub, map_sub, map_sub, hφψ]
  abel

end TateFactoring

end ModularCurve.KwF4gRRTate

end

set_option autoImplicit false
set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

section CorrectedCarrier

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

def kaehlerPullback (ωE : Ω[E⁄K]) : Ω[F⁄K] :=
  KaehlerDifferential.map K K E F ωE

variable {K F E}

variable (K F E)
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

end CorrectedCarrier

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def regularSubmodule (w : Place K F) (ωF : Ω[F⁄K]) : Submodule K F where
  carrier := {f : F | f * w.differentialCoeff ωF ∈ w.toValuationSubring}
  zero_mem' := by simp only [Set.mem_setOf_eq, zero_mul]; exact zero_mem _
  add_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq, add_mul]; exact add_mem hf hg
  smul_mem' c f hf := by
    simp only [Set.mem_setOf_eq, Algebra.smul_def, mul_assoc]
    exact mul_mem (w.algebraMap_mem' c) hf

end Place

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

section KaehlerCotrace

variable (K E F : Type*) [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

abbrev kaehlerCotrace : Ω[E⁄K] →ₗ[E] Ω[F⁄K] :=
  KaehlerDifferential.map K K E F

variable {K E F}

end KaehlerCotrace

end AlgebraicCurve

end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain

noncomputable section

namespace AlgebraicCurve

section LocalResidueCompletion

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

variable [HasCanonicalLocalResidueKStar K E]

def kwHgfV352_localResidueCompletion (v : Place K E) (xh : v.adicCompletion) :
    v.ResidueField :=
  v.localResidue (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose

end LocalResidueCompletion

section CompletionTraceAt

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

def kwHgfV352_completionTraceAt [FiniteDimensional E F]
    (v : Place K E) (w' : Place K F) (hw' : w' ∈ v.fiber F) (g : F) :
    v.adicCompletion :=
  Place.mem_fiber.mp hw' ▸ kw_ffgc_completionTraceF' E w' g

end CompletionTraceAt

section MPGKPowBasisLocalMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

def KwHgfV352R3MPGKPowBasisLocal : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [∀ w : Place K F, w.FiniteResidue]
    [FiniteDimensional E F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F)
    (_ : ∀ w'' ∈ v.fiber F,
      w''.differentialCoeff (kaehlerPullback K F E ωE) ∈ w''.toValuationSubring)
    (θ : F) (_ : ∀ w' ∈ v.fiber F, θ ∈ w'.toValuationSubring)
    (π : F) (_ : π ≠ 0) (_ : w.ord π = 1)
    (_ : ∀ w' ∈ v.fiber F, w' ≠ w → w'.ord π = 0)
    (j : ℕ) (_ : j < Module.finrank K w.ResidueField) (k : ℕ),
    kaehlerResidueTerm (kaehlerPullback K F E ωE)
        (diagonalHom K F (θ ^ j * (π ^ (k + 1))⁻¹)) w
      = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            (kwHgfV352_completionTraceAt v w hw (θ ^ j * (π ^ (k + 1))⁻¹)
              * algebraMap E v.adicCompletion (v.differentialCoeff ωE)))

end MPGKPowBasisLocalMint

section CompletionTraceSumMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

def KwHgfV352CompletionTraceSum : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (g : F),
    algebraMap E v.adicCompletion (Algebra.trace E F g)
      = ∑ w' ∈ (v.fiber F).attach, kwHgfV352_completionTraceAt v w'.1 w'.2 g

end CompletionTraceSumMint

end AlgebraicCurve

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place LinearMap Submodule
open ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve.KwF4gRRTate

section TateProj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

def adicIntegersKSubmod : Submodule K u.adicCompletion where
  carrier := u.adicCompletionIntegers
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c x hx := by
    rw [Algebra.smul_def]
    exact mul_mem (by
      rw [IsScalarTower.algebraMap_apply K L u.adicCompletion]
      exact (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr
        (u.algebraMap_mem' c)) hx

def tateProj : u.adicCompletion →ₗ[K] u.adicCompletion :=
  letI B := Classical.choose (Submodule.exists_isCompl (adicIntegersKSubmod u))
  (adicIntegersKSubmod u).subtype ∘ₗ
    Submodule.projectionOnto (adicIntegersKSubmod u) B
      (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u)))

end TateProj

section TateResDef

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

abbrev lmulK (fh : u.adicCompletion) : u.adicCompletion →ₗ[K] u.adicCompletion :=
  (Algebra.lmul K u.adicCompletion) fh

def tateRes (fh gh : u.adicCompletion)
    [FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh)))] : K :=
  tateCommTrace (tateProj u) (lmulK u fh) (lmulK u gh)

end TateResDef

section TateAtoms

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

def KwF4gRRTateCommFinite : Prop :=
  ∀ (u : Place K L) (fh gh : u.adicCompletion),
    FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh)))

variable [HasCanonicalLocalResidueKStar K L]

def KwF4gRRTateAgreement (hfin : KwF4gRRTateCommFinite K L) : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (fh : u.adicCompletion),
    haveI := hfin u fh (algebraMap L u.adicCompletion u.uniformizer)
    tateRes u fh (algebraMap L u.adicCompletion u.uniformizer)
      = Algebra.trace K u.ResidueField (kwHgfV352_localResidueCompletion u fh)

variable (F E : Type*) [Field F] [Algebra K F] [Field E] [Algebra K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

def KwF4gRRTateChainRule (hfinF : KwF4gRRTateCommFinite K F) : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    [Nontrivial Ω[E⁄K]] [Nontrivial Ω[F⁄K]]
    (v : Place K E) [v.DCoordGenerates] (w : Place K F) [w.DCoordGenerates]
    (_ : w ∈ v.fiber F) (fh : w.adicCompletion),
    haveI := hfinF w fh (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
    haveI := hfinF w (fh * algebraMap F w.adicCompletion
      (w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
      (algebraMap F w.adicCompletion w.uniformizer)
    tateRes w fh (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
      = tateRes w (fh * algebraMap F w.adicCompletion
          (w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
          (algebraMap F w.adicCompletion w.uniformizer)

def KwF4gRRTateTraceCompat (hfinF : KwF4gRRTateCommFinite K F)
    (hfinE : KwF4gRRTateCommFinite K E) : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F) (g : F),
    haveI := hfinF w (algebraMap F w.adicCompletion g)
      (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
    haveI := hfinE v (kwHgfV352_completionTraceAt v w hw g)
      (algebraMap E v.adicCompletion v.uniformizer)
    tateRes w (algebraMap F w.adicCompletion g)
        (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
      = tateRes v (kwHgfV352_completionTraceAt v w hw g)
          (algebraMap E v.adicCompletion v.uniformizer)

end TateAtoms

end ModularCurve.KwF4gRRTate

end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place FunctionField KaehlerDifferential

noncomputable section

namespace ModularCurve.KwF4R1V391a

section Mint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

def KwF4R1V391aResidueTraceCompletionCommute : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    [∀ w : Place K F, w.FiniteResidue] [FiniteDimensional E F]
    [Nontrivial Ω[E⁄K]] (v : Place K E) [v.DCoordGenerates]
    (w : Place K F) [w.DCoordGenerates] (_ : w ∈ v.fiber F) (g : F),
    kaehlerResidueTerm (kaehlerPullback K F E v.dCoord) (diagonalHom K F g) w
      = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            (kwHgfV352_completionTraceAt v w ‹w ∈ v.fiber F› g))

end Mint

end ModularCurve.KwF4R1V391a

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

namespace AlgebraicCurve

open scoped Polynomial

section KCurrencyRow

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

def FiberKaehlerCotraceResidueIdentityK : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0),
    ∃ RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK,
      ∀ (v : Place K E) (f : F),
        ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F f) w
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F f)) v

end KCurrencyRow

end AlgebraicCurve

end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

namespace AlgebraicCurve

open scoped Polynomial

section KCurrencyRowA

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

def CotraceResidueIdentityOnFiberLocalizedK : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0),
    ∃ RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK,
      ∀ (v : Place K E) (p : F),
        (∀ w₁ ∈ v.fiber F, ∀ w₂ ∈ v.fiber F,
          p ∉ w₁.regularSubmodule (kaehlerPullback K F E ωE) →
          p ∉ w₂.regularSubmodule (kaehlerPullback K F E ωE) → w₁ = w₂) →
        ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F p) w
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v

end KCurrencyRowA

end AlgebraicCurve

end
