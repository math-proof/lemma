module

public import Mathlib
public import Theorem.Submodule.Repartitions
public import Structure.AlgebraicCurve_AdelicIndex
public import Abbrev.AlgebraicCurve_AdelicIndex

@[expose] public section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable {D E : Divisor K F}

def ConstantsAreBase (K F : Type*) [Field K] [Field F] [Algebra K F] : Prop :=
  LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F)

def adeleBdd (D : Divisor K F) : Submodule K (Place K F → F) where
  carrier := {α | ∀ v : Place K F, v.adicValuation (α v) ≤ WithZero.exp (D v)}
  add_mem' := fun {α β} hα hβ v =>
    (v.adicValuation.map_add (α v) (β v)).trans (max_le (hα v) (hβ v))
  zero_mem' := fun v => by rw [Pi.zero_apply, Valuation.map_zero]; exact zero_le
  smul_mem' := fun c α hα v => by
    rw [Pi.smul_apply, Algebra.smul_def, Valuation.map_mul]
    calc v.adicValuation (algebraMap K F c) * v.adicValuation (α v)
        ≤ 1 * v.adicValuation (α v) := by gcongr; exact v.adicValuation_algebraMap_le_one c
      _ = v.adicValuation (α v) := one_mul _
      _ ≤ WithZero.exp (D v) := hα v

variable {D E : Divisor K F}

variable (K F) in

def diagonalHom : F →ₗ[K] (Place K F → F) where
  toFun f := fun _ => f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (K F) in

def adeleSpace : Submodule K (Place K F → F) := ⨆ D : Divisor K F, adeleBdd D

variable (K F) in

def globalSub : Submodule K (Place K F → F) := LinearMap.range (diagonalHom K F)

def lSpaceEquivAdeleBddInfGlobal [Nonempty (Place K F)] (D : Divisor K F) :
    LSpace D ≃ₗ[K] (adeleBdd D ⊓ globalSub K F : Submodule K (Place K F → F)) :=
  (Submodule.equivMapOfInjective (diagonalHom K F) diagonalHom_injective (LSpace D)).trans
    (LinearEquiv.ofEq _ _ (map_diagonal_lSpace D))

def indexOfSpecialty (D : Divisor K F) : ℕ :=
  Module.finrank K
    ((adeleSpace K F) ⧸
      ((adeleBdd D).comap (adeleSpace K F).subtype ⊔
        (globalSub K F).comap (adeleSpace K F).subtype))

variable (K F) in

abbrev adeleBddPrincipal (D : Divisor K F) : Submodule K (adeleSpace K F) :=
  (adeleBdd D).comap (adeleSpace K F).subtype ⊔
    (globalSub K F).comap (adeleSpace K F).subtype

def omegaSpace (D : Divisor K F) : Submodule K (Module.Dual K (adeleSpace K F)) :=
  (adeleBddPrincipal K F D).dualAnnihilator

def omegaSpaceEquivIndexDual (D : Divisor K F) :
    omegaSpace D ≃ₗ[K] Module.Dual K (adeleSpace K F ⧸ adeleBddPrincipal K F D) :=
  (Submodule.dualQuotEquivDualAnnihilator (adeleBddPrincipal K F D)).symm

variable (K F) in

def weilDifferentialModule : Submodule K (Module.Dual K (adeleSpace K F)) :=
  ⨆ D : Divisor K F, omegaSpace D

variable (K) in

def mulAdele (f : F) : (Place K F → F) →ₗ[K] (Place K F → F) where
  toFun α := fun v => f * α v
  map_add' α β := funext fun v => mul_add f (α v) (β v)
  map_smul' c α := funext fun v => by
    simp only [Pi.smul_apply, Algebra.smul_def, RingHom.id_apply]; ring

variable (K F) in

def adeleSpaceMul [HasPrincipalDivisors K F] (f : F) :
    adeleSpace K F →ₗ[K] adeleSpace K F :=
  (mulAdele K f).restrict fun _ => mulAdele_mem_adeleSpace f

variable (K F) in

def weilSmul [HasPrincipalDivisors K F] (f : F) :
    Module.Dual K (adeleSpace K F) →ₗ[K] Module.Dual K (adeleSpace K F) :=
  (adeleSpaceMul K F f).dualMap

variable (K F) in

def residuePairing [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) :
    LSpace (W - D) →ₗ[K] omegaSpace D where
  toFun g := ⟨weilSmul K F (g : F) φ, weilSmul_mem_omegaSpace_of_mem_lSpace hφ g.2⟩
  map_add' g₁ g₂ := by
    refine Subtype.ext ?_
    show weilSmul K F ((g₁ : F) + (g₂ : F)) φ
      = weilSmul K F (g₁ : F) φ + weilSmul K F (g₂ : F) φ
    ext α; simp only [weilSmul_apply, LinearMap.add_apply]
    rw [← map_add]; congr 1
    exact Subtype.ext (funext fun v => by simp [add_mul])
  map_smul' c g := by
    refine Subtype.ext ?_
    show weilSmul K F (c • (g : F)) φ = c • weilSmul K F (g : F) φ
    ext α; simp only [weilSmul_apply, LinearMap.smul_apply]
    rw [← map_smul]; congr 1
    exact Subtype.ext (funext fun v => by simp [Algebra.smul_def]; ring)

variable (K F)

def WeilDifferentialRankOne [HasPrincipalDivisors K F] : Prop :=
  ∀ {φ : Module.Dual K (adeleSpace K F)}, φ ∈ weilDifferentialModule K F → φ ≠ 0 →
    ∀ {μ : Module.Dual K (adeleSpace K F)}, μ ∈ weilDifferentialModule K F →
      ∃! f : F, μ = weilSmul K F f φ

def HasWeilCanonicalDivisor : Prop :=
  ∀ {φ : Module.Dual K (adeleSpace K F)}, φ ∈ weilDifferentialModule K F → φ ≠ 0 →
    ∃ W : Divisor K F, φ ∈ omegaSpace W ∧ ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ W

variable {K F}


variable (K F) in

def RiemannGenusReached (γ : ℤ) : Prop :=
  Nonempty (Place K F) ∧ FiniteDimensional K (LSpace (0 : Divisor K F)) ∧
    ∃ D₀ : Divisor K F, RiemannGenusReachedAt γ D₀

variable (K F) in

def StichtenothGenusExists : Prop :=
  Nonempty (Place K F) ∧ FiniteDimensional K (LSpace (0 : Divisor K F)) ∧
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀

variable (K F) in

def RiemannGenusBounded : Prop :=
  ∃ γ : ℤ, ∀ D : Divisor K F, Divisor.degree D - (ell D : ℤ) ≤ γ

variable (K F) in

def IndexOfSpecialtyFinite : Prop :=
  ∃ D₀ : Divisor K F, Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D₀)

end AlgebraicCurve

end

end
