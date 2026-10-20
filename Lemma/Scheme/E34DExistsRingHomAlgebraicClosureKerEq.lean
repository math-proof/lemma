import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma finite_of_moduleFinite_int_charP {A : Type*} [CommRing A] [Module.Finite ℤ A]
    {p : ℕ} [Fact p.Prime] [CharP A p] : Finite A := by
  let _ : Algebra (ZMod p) A := (ZMod.castHom (dvd_refl p) A).toAlgebra
  let _ : IsScalarTower ℤ (ZMod p) A :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let _ : Module.Finite (ZMod p) A := Module.Finite.of_restrictScalars_finite ℤ (ZMod p) A
  exact Module.finite_of_finite (ZMod p)
variable {R : Type*} [CommRing R]
variable {p : ℕ} [hp : Fact p.Prime]
private lemma charP_quotient {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : R) ∈ 𝔪) :
    CharP (R ⧸ 𝔪) p := by
  let _ := h𝔪
  have hp0 : (p : R ⧸ 𝔪) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq_zero_iff_mem]; exact hp𝔪
  exact (CharP.charP_iff_prime_eq_zero hp.out).mpr hp0
private lemma finite_quotient [Module.Finite ℤ R] {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : (p : R) ∈ 𝔪) : Finite (R ⧸ 𝔪) := by
  let _ := charP_quotient h𝔪 hp𝔪
  let _ : Module.Finite ℤ (R ⧸ 𝔪) := Module.Finite.trans R (R ⧸ 𝔪)
  exact finite_of_moduleFinite_int_charP
private lemma exists_ringHom_algClosure_ker_eq_aux [Module.Finite ℤ R]
    {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : R) ∈ 𝔪) :
    ∃ φ : R →+* AlgebraicClosure (ZMod p), RingHom.ker φ = 𝔪 := by
  let _ := h𝔪
  let _ : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let _ := charP_quotient h𝔪 hp𝔪
  let _ := finite_quotient h𝔪 hp𝔪
  let _ : Algebra (ZMod p) (R ⧸ 𝔪) := (ZMod.castHom (dvd_refl p) (R ⧸ 𝔪)).toAlgebra
  let ψ : (R ⧸ 𝔪) →ₐ[ZMod p] AlgebraicClosure (ZMod p) := IsAlgClosed.lift
  have hψinj : Function.Injective (ψ : (R ⧸ 𝔪) →+* AlgebraicClosure (ZMod p)) :=
    RingHom.injective _
  refine ⟨(ψ : (R ⧸ 𝔪) →+* AlgebraicClosure (ZMod p)).comp (Ideal.Quotient.mk 𝔪), ?_⟩
  rw [RingHom.ker_comp_of_injective (Ideal.Quotient.mk 𝔪) hψinj, Ideal.mk_ker]
/--
[E34D_exists_ringHom_algebraicClosure_ker_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_E34D_exists_ringHom_algebraicClosure_ker_eq.lean)
-/
@[path]
private lemma main {R : Type*} [CommRing R] {p : ℕ}
    [hp : Fact p.Prime] [Module.Finite ℤ R]
    {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : R) ∈ 𝔪) :
    ∃ φ : R →+* AlgebraicClosure (ZMod p), RingHom.ker φ = 𝔪 :=
  exists_ringHom_algClosure_ker_eq_aux h𝔪 hp𝔪

-- created on 2026-10-20
