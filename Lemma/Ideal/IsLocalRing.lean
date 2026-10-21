import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private noncomputable def toIntegralClosure (R F L : Type*) [CommRing R] [Field F] [Field L]
    [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L] :
    ↥(integralClosure R F) →ₐ[R] ↥(integralClosure R L) :=
  ((IsScalarTower.toAlgHom R F L).comp (integralClosure R F).val).codRestrict
    (integralClosure R L) (fun x => by
      show IsIntegral R ((IsScalarTower.toAlgHom R F L) (x : F))
      exact IsIntegral.map (IsScalarTower.toAlgHom R F L) x.2)
private lemma coe_toIntegralClosure (R F L : Type*) [CommRing R] [Field F] [Field L]
    [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
    (x : ↥(integralClosure R F)) :
    ((toIntegralClosure R F L x : ↥(integralClosure R L)) : L) = algebraMap F L (x : F) := rfl
private lemma toIntegralClosure_injective (R F L : Type*) [CommRing R] [Field F] [Field L]
    [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L] :
    Function.Injective (toIntegralClosure R F L) := by
  intro x y hxy
  apply Subtype.ext
  apply (algebraMap F L).injective
  have := congrArg (fun z : ↥(integralClosure R L) => (z : L)) hxy
  simpa [coe_toIntegralClosure] using this
/--
[integralClosure_isLocalRing_of_forall_isMaximal_exists_comap_galRestrict_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_integralClosure_isLocalRing_of_forall_isMaximal_exists_comap_galRestrict_eq.lean)
-/
@[path]
private lemma main
    {R F L : Type*} [CommRing R] [IsDomain R] [Field F] [Field L]
    [Algebra R F] [IsFractionRing R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
    [FiniteDimensional F L]
    (htrans : ∀ M₁ M₂ : Ideal ↥(integralClosure R L), M₁.IsMaximal → M₂.IsMaximal →
      ∃ σ : L ≃ₐ[F] L, M₂ = Ideal.comap (galRestrict R F L ↥(integralClosure R L) σ) M₁) :
    IsLocalRing ↥(integralClosure R F) := by
  classical
  let f : ↥(integralClosure R F) →ₐ[R] ↥(integralClosure R L) := toIntegralClosure R F L
  let _ : Algebra ↥(integralClosure R F) ↥(integralClosure R L) := f.toRingHom.toAlgebra
  have hf : ∀ a, algebraMap ↥(integralClosure R F) ↥(integralClosure R L) a = f a := fun _ => rfl
  let _ : IsScalarTower R ↥(integralClosure R F) ↥(integralClosure R L) :=
    IsScalarTower.of_algebraMap_eq (fun r => by rw [hf]; exact (f.commutes r).symm)
  let _ : Algebra.IsIntegral ↥(integralClosure R F) ↥(integralClosure R L) :=
    Algebra.IsIntegral.tower_top (R := R)
  have hinj : Function.Injective (algebraMap ↥(integralClosure R F) ↥(integralClosure R L)) :=
    toIntegralClosure_injective R F L
  have hker : RingHom.ker (algebraMap ↥(integralClosure R F) ↥(integralClosure R L)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have key : ∀ (σ : L ≃ₐ[F] L) (a : ↥(integralClosure R F)),
      galRestrict R F L ↥(integralClosure R L) σ
        (algebraMap ↥(integralClosure R F) ↥(integralClosure R L) a) =
        algebraMap ↥(integralClosure R F) ↥(integralClosure R L) a := by
    intro σ a
    apply Subtype.ext
    have h1 := algebraMap_galRestrict_apply (A := R) (K := F) (L := L)
      (B := ↥(integralClosure R L)) σ
      (algebraMap ↥(integralClosure R F) ↥(integralClosure R L) a)
    change ((galRestrict R F L ↥(integralClosure R L) σ
        (algebraMap ↥(integralClosure R F) ↥(integralClosure R L) a) : ↥(integralClosure R L)) : L)
        = σ ((algebraMap ↥(integralClosure R F) ↥(integralClosure R L) a : ↥(integralClosure R L)) : L) at h1
    rw [h1, hf, coe_toIntegralClosure]
    exact σ.commutes (a : F)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal ↥(integralClosure R F)
  refine IsLocalRing.of_unique_max_ideal ⟨m, hm, fun m' hm' => ?_⟩
  obtain ⟨M, hM, hMm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := ↥(integralClosure R L)) m (by rw [hker]; exact bot_le)
  obtain ⟨M', hM', hM'm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := ↥(integralClosure R L)) m' (by rw [hker]; exact bot_le)
  obtain ⟨σ, hσ⟩ := htrans M M' hM hM'
  rw [← hM'm, ← hMm, hσ]
  ext a
  simp only [Ideal.mem_comap]
  rw [key]

-- created on 2026-10-20
