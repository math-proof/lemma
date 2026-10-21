import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  [CommRing R]
  [CommRing A] [Algebra R A] [Module.Finite R A]
  (S : Subalgebra R A)
  (k : Type*) [Field k] [IsAlgClosed k] [Algebra R k]
  (φ : AlgHom R ↥S k) :
  -- imply
  ∃ ψ : AlgHom R A k, ψ.comp S.val = φ := by
  -- proof
  classical
  let _ : Module.Finite S A := Module.Finite.of_restrictScalars_finite R S A
  let _ : Algebra.IsIntegral S A := Algebra.IsIntegral.of_finite S A
  let 𝔭 : Ideal S := RingHom.ker (φ : RingHom ↥S k)
  let h𝔭 : 𝔭.IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, -, hQ, hQover⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭 (⊥ : Ideal A)
    (Ideal.comap_bot_le_of_injective _ Subtype.val_injective)
  let _ := hQ
  let hLO : Q.LiesOver 𝔭 := ⟨hQover.symm⟩
  let φbar : AlgHom R (S ⧸ 𝔭) k := Ideal.Quotient.liftₐ 𝔭 φ (fun a ha => ha)
  let _ : Algebra (S ⧸ 𝔭) k := φbar.toRingHom.toAlgebra
  let _ : IsScalarTower R (S ⧸ 𝔭) k := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap R k r = φbar (algebraMap R (S ⧸ 𝔭) r)
    rw [AlgHom.commutes]
  have hinj : Function.Injective (algebraMap (S ⧸ 𝔭) k) := by
    show Function.Injective φbar
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr hx
  let _ : IsDomain (S ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  let _ : IsDomain (A ⧸ Q) := Ideal.Quotient.isDomain Q
  let _ : Module.IsTorsionFree (S ⧸ 𝔭) k := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
  let _ : Module.IsTorsionFree (S ⧸ 𝔭) (A ⧸ Q) :=
    (Module.isTorsionFree_iff_faithfulSMul).mpr (Ideal.Quotient.instFaithfulSMul Q 𝔭)
  let _ : Algebra.IsIntegral (S ⧸ 𝔭) (A ⧸ Q) := Ideal.Quotient.algebra_isIntegral_of_liesOver Q 𝔭
  let _ : Nontrivial (S ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.mpr h𝔭.ne_top
  let _ : Algebra.IsAlgebraic (S ⧸ 𝔭) (A ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let ψ' : AlgHom (S ⧸ 𝔭) (A ⧸ Q) k := IsAlgClosed.lift
  refine ⟨(ψ'.restrictScalars R).comp (Ideal.Quotient.mkₐ R Q), ?_⟩
  apply AlgHom.ext
  intro s
  show ψ' (Ideal.Quotient.mk Q (s : A)) = φ s
  have h1 : Ideal.Quotient.mk Q (s : A) = algebraMap (S ⧸ 𝔭) (A ⧸ Q) (Ideal.Quotient.mk 𝔭 s) := rfl
  rw [h1, AlgHom.commutes]
  rfl


-- created on 2026-10-20
