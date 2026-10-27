import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma finite_of_moduleFinite_int_charP
  {A : Type u} [CommRing A] [Module.Finite ℤ A]
  {p : ℕ} [Fact p.Prime] [CharP A p] :
  -- imply
  Finite A := by
  -- proof
  let _ : Algebra (ZMod p) A := (ZMod.castHom (dvd_refl p) A).toAlgebra
  let _ : IsScalarTower ℤ (ZMod p) A := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let _ : Module.Finite (ZMod p) A := Module.Finite.of_restrictScalars_finite ℤ (ZMod p) A
  apply Module.finite_of_finite (ZMod p)

private lemma charP_quotient
  {R : Type u} [CommRing R]
  {p : ℕ} [hp : Fact p.Prime]
  {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : R) ∈ 𝔪) :
  -- imply
  CharP (R ⧸ 𝔪) p := by
  -- proof
  let _ := h𝔪
  refine (CharP.charP_iff_prime_eq_zero hp.out).mpr ?_
  rw [← map_natCast (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq_zero_iff_mem]
  apply hp𝔪

private lemma finite_quotient
  {R : Type u} [CommRing R] [Module.Finite ℤ R]
  {p : ℕ} [Fact p.Prime]
  {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : R) ∈ 𝔪) :
  -- imply
  Finite (R ⧸ 𝔪) := by
  -- proof
  let _ := charP_quotient h𝔪 hp𝔪
  let _ : Module.Finite ℤ (R ⧸ 𝔪) := Module.Finite.trans R (R ⧸ 𝔪)
  apply finite_of_moduleFinite_int_charP

private lemma exists_ringHom_algClosure_ker_eq_aux
  {R : Type u} [CommRing R] [Module.Finite ℤ R]
  {p : ℕ} [Fact p.Prime]
  {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : R) ∈ 𝔪) :
  -- imply
  ∃ φ : RingHom R (AlgebraicClosure (ZMod p)), RingHom.ker φ = 𝔪 := by
  -- proof
  let _ := h𝔪
  let _ : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let _ := charP_quotient h𝔪 hp𝔪
  let _ := finite_quotient h𝔪 hp𝔪
  let _ : Algebra (ZMod p) (R ⧸ 𝔪) := (ZMod.castHom (dvd_refl p) (R ⧸ 𝔪)).toAlgebra
  let ψ : AlgHom (ZMod p) (R ⧸ 𝔪) (AlgebraicClosure (ZMod p)) := IsAlgClosed.lift
  have hψinj : Function.Injective (ψ : RingHom (R ⧸ 𝔪) (AlgebraicClosure (ZMod p))) := RingHom.injective _
  refine ⟨(ψ : RingHom (R ⧸ 𝔪) (AlgebraicClosure (ZMod p))).comp (Ideal.Quotient.mk 𝔪), ?_⟩
  rw [RingHom.ker_comp_of_injective (Ideal.Quotient.mk 𝔪) hψinj, Ideal.mk_ker]

/--
[E34D_exists_ringHom_algebraicClosure_ker_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_E34D_exists_ringHom_algebraicClosure_ker_eq.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {p : ℕ} [Fact p.Prime] [Module.Finite ℤ R]
  {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : R) ∈ 𝔪) :
  -- imply
  ∃ φ : RingHom R (AlgebraicClosure (ZMod p)), RingHom.ker φ = 𝔪 :=
  exists_ringHom_algClosure_ker_eq_aux h𝔪 hp𝔪


-- created on 2026-10-20
