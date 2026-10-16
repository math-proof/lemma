import Mathlib
import sympy.Basic
open IsLocalRing
open scoped TensorProduct


/--
[Algebra_TensorProduct_ker_lift_le_jacobson_of_isLocalRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_ker_lift_le_jacobson_of_isLocalRing.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsLocalRing R]
  {C : Type v} [CommRing C] [Algebra R C] [Module.Finite R C]
  {D : Type w} [CommRing D] [Algebra R D] [Module.Finite R D] [IsLocalRing D]
  {ε : D →ₐ[R] R} :
-- imply
  RingHom.ker (Algebra.TensorProduct.lift (AlgHom.id R C) ((Algebra.ofId R C).comp ε)
      (fun _ _ => Commute.all _ _) : C ⊗[R] D →ₐ[R] C) ≤ Ideal.jacobson ⊥ := by
-- proof
  classical
  let _ : Algebra.IsIntegral R D := Algebra.IsIntegral.of_finite R D
  have map_maximalIdeal_le : (maximalIdeal R).map (algebraMap R D) ≤ maximalIdeal D := by
    rw [Ideal.map_le_iff_le_comap]
    have : (Ideal.comap (algebraMap R D) (maximalIdeal D)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal D)
    rw [IsLocalRing.eq_maximalIdeal this]
  have exists_maximalIdeal_pow_le : ∃ N : ℕ, (maximalIdeal D) ^ N ≤ (maximalIdeal R).map (algebraMap R D) := by
    set J : Ideal D := (maximalIdeal R).map (algebraMap R D) with hJ
    have hJle : J ≤ maximalIdeal D := map_maximalIdeal_le
    have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal D).ne_top (top_le_iff.mp (h ▸ hJle))
    let _ : Nontrivial (D ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
    let _ : IsLocalRing (D ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    let _ : Module.Finite (R ⧸ maximalIdeal R) (D ⧸ J) :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ maximalIdeal R) (D ⧸ J)
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
    let _ : IsArtinianRing (D ⧸ J) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (D ⧸ J)
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := D ⧸ J)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
    refine ⟨N, ?_⟩
    have hmap : (maximalIdeal D).map (Ideal.Quotient.mk J) ≤ maximalIdeal (D ⧸ J) := by
      apply IsLocalRing.le_maximalIdeal
      intro htop
      have h1 := Ideal.comap_map_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
        (maximalIdeal D)
      rw [htop, Ideal.comap_top] at h1
      have h2 : maximalIdeal D ⊔ Ideal.comap (Ideal.Quotient.mk J) ⊥ ≤ maximalIdeal D :=
        sup_le le_rfl (by rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker])
      rw [← h1] at h2
      apply (maximalIdeal.isMaximal D).ne_top (top_le_iff.mp h2)
    have h0 : ((maximalIdeal D) ^ N).map (Ideal.Quotient.mk J) = ⊥ := by
      rw [Ideal.map_pow]
      apply le_bot_iff.mp ((Ideal.pow_right_mono hmap N).trans (le_of_eq hN))
    rwa [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h0
  set f : C ⊗[R] D →ₐ[R] C := Algebra.TensorProduct.lift (AlgHom.id R C)
    ((Algebra.ofId R C).comp ε) (fun _ _ => Commute.all _ _) with hfdef
  have hε : Function.Surjective ε := fun r => ⟨algebraMap R D r, AlgHom.commutes ε r⟩
  have hf : ∀ x, f x = Algebra.TensorProduct.rid R R C
    (Algebra.TensorProduct.map (AlgHom.id R C) ε x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c d =>
      simp only [hfdef, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
        Algebra.ofId_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul,
        Algebra.smul_def, mul_comm]
    | add x y hx hy =>
      rw [map_add, hx, hy, map_add, map_add]
  have hker : RingHom.ker f = (RingHom.ker ε).map
    (Algebra.TensorProduct.includeRight : D →ₐ[R] C ⊗[R] D) := by
    rw [← Algebra.TensorProduct.lTensor_ker ε hε]
    ext x
    rw [RingHom.mem_ker, RingHom.mem_ker, hf, map_eq_zero_iff _ (Algebra.TensorProduct.rid R R C).injective]
  have hI : RingHom.ker ε ≤ maximalIdeal D := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ε)
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le
  have hK : (RingHom.ker f) ^ N ≤ (maximalIdeal R).map (algebraMap R (C ⊗[R] D)) := by
    rw [hker, ← Ideal.map_pow]
    refine (Ideal.map_mono ((Ideal.pow_right_mono hI N).trans hN)).trans ?_
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have : (Algebra.TensorProduct.includeRight : D →ₐ[R] C ⊗[R] D) (algebraMap R D r) =
        algebraMap R (C ⊗[R] D) r := AlgHom.commutes _ r
    rw [this]
    apply Ideal.mem_map_of_mem _ hr
  intro x hx
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro M ⟨-, hM⟩
  let _ : Algebra.IsIntegral R (C ⊗[R] D) := Algebra.IsIntegral.of_finite R (C ⊗[R] D)
  let _ : M.IsMaximal := hM
  have hcomap : (M.comap (algebraMap R (C ⊗[R] D))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) (S := C ⊗[R] D) M
  apply hM.isPrime.mem_of_pow_mem N
  ·
    apply show (maximalIdeal R).map (algebraMap R (C ⊗[R] D)) ≤ M by
      rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal hcomap]
    apply hK (Ideal.pow_mem_pow hx N)


-- created on 2026-10-16
