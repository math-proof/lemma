import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[RingHom_exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
  [Field K] [IsAlgClosed K]
  (χ : RingHom R K)
  (Q : Ideal S) [Q.IsPrime]
  -- given
  (hQ : Q.comap (algebraMap R S) = RingHom.ker χ) :
  -- imply
  ∃ χ' : RingHom S K, χ'.comp (algebraMap R S) = χ ∧ RingHom.ker χ' = Q := by
  -- proof
  classical
  set P : Ideal R := Q.comap (algebraMap R S) with hPdef
  let hP : P.IsPrime := Ideal.IsPrime.comap _
  have hle : ∀ a ∈ P, χ a = 0 := fun a ha => RingHom.mem_ker.mp (hQ ▸ ha)
  let ψ : RingHom (R ⧸ P) K := Ideal.Quotient.lift P χ hle
  have hψinj : Function.Injective ψ :=
    RingHom.lift_injective_of_ker_le_ideal P hle hQ.ge
  let _ : Algebra (R ⧸ P) K := ψ.toAlgebra
  let _ : FaithfulSMul (R ⧸ P) K :=
    (faithfulSMul_iff_algebraMap_injective _ K).mpr hψinj
  let _ : FaithfulSMul (R ⧸ P) (S ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  let _ : Algebra.IsIntegral (R ⧸ P) (S ⧸ Q) := Algebra.IsIntegral.quotient
  let _ : Module.IsTorsionFree (R ⧸ P) (S ⧸ Q) :=
    @FaithfulSMul.to_isTorsionFree _ _ _ _ _ _ inferInstance inferInstance
  let _ : Module.IsTorsionFree (R ⧸ P) K :=
    @FaithfulSMul.to_isTorsionFree _ _ _ _ _ _ inferInstance inferInstance
  let _ : Algebra.IsAlgebraic (R ⧸ P) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let θ : AlgHom (R ⧸ P) (S ⧸ Q) K := IsAlgClosed.lift
  refine ⟨θ.toRingHom.comp (Ideal.Quotient.mk Q), ?_, ?_⟩
  ·
    ext a
    change θ (Ideal.Quotient.mk Q (algebraMap R S a)) = χ a
    have h1 : Ideal.Quotient.mk Q (algebraMap R S a) = algebraMap (R ⧸ P) (S ⧸ Q) (Ideal.Quotient.mk P a) := rfl
    rw [h1, θ.commutes]
    apply Ideal.Quotient.lift_mk P χ _
  ·
    have hker : RingHom.ker θ.toRingHom = ⊥ := by
      apply Ideal.eq_bot_of_under_eq_bot (R := R ⧸ P)
      rw [eq_bot_iff]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker] at hx
      change θ (algebraMap (R ⧸ P) (S ⧸ Q) x) = 0 at hx
      rw [θ.commutes] at hx
      apply (Ideal.mem_bot).mpr (hψinj (by rw [map_zero]; apply hx))
    rw [← RingHom.comap_ker, hker, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]


-- created on 2026-10-20
