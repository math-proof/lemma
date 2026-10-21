import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[integralClosure_moduleFinite_of_isReduced_of_charZero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_integralClosure_moduleFinite_of_isReduced_of_charZero.lean)
-/
@[path]
private lemma main
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [CommRing L] [IsReduced L] [Algebra K L] [Module.Finite K L]
    [Algebra R L] [IsScalarTower R K L] :
    Module.Finite R (integralClosure R L) := by
  classical
  let _ : IsArtinianRing L := IsArtinianRing.of_finite K L
  let hmax : ∀ j : MaximalSpectrum L, j.asIdeal.IsMaximal := fun j => j.isMaximal
  have hfinK : ∀ j : MaximalSpectrum L, Module.Finite K (L ⧸ j.asIdeal) := fun j =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K j.asIdeal).toLinearMap (Ideal.Quotient.mkₐ_surjective K _)
  have hfin : ∀ j : MaximalSpectrum L, Module.Finite R ↥(integralClosure R (L ⧸ j.asIdeal)) := fun j => by
    let _ := hfinK j
    let _ : j.asIdeal.IsMaximal := j.isMaximal
    let _ : Field (L ⧸ j.asIdeal) := Ideal.Quotient.field j.asIdeal
    exact IsIntegralClosure.finite R K (L ⧸ j.asIdeal) ↥(integralClosure R (L ⧸ j.asIdeal))
  let _ : Module.Finite R ((j : MaximalSpectrum L) → ↥(integralClosure R (L ⧸ j.asIdeal))) := Module.Finite.pi
  let φ : ↥(integralClosure R L) →ₗ[R] ((j : MaximalSpectrum L) → ↥(integralClosure R (L ⧸ j.asIdeal))) :=
    LinearMap.pi fun j =>
      { toFun := fun x => ⟨Ideal.Quotient.mk j.asIdeal (x : L),
          (x.2.map (Ideal.Quotient.mkₐ R j.asIdeal) : IsIntegral R (Ideal.Quotient.mkₐ R j.asIdeal (x : L)))⟩
        map_add' := fun x y => Subtype.ext (by simp)
        map_smul' := fun r x => Subtype.ext (by simp [Algebra.smul_def]) }
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hxj : ∀ j : MaximalSpectrum L, (x : L) ∈ j.asIdeal := fun j => by
      have := congrArg Subtype.val (congrFun hx j)
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    have hjac : (x : L) ∈ (⊥ : Ideal L).jacobson :=
      Ideal.mem_sInf.mpr fun J hJ => hxj ⟨J, hJ.2⟩
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := L)
    have hxn : (x : L) ^ n = 0 := by
      have : (x : L) ^ n ∈ (⊥ : Ideal L).jacobson ^ n := Ideal.pow_mem_pow hjac n
      rw [hn] at this
      exact this
    exact Subtype.ext (IsReduced.eq_zero (x : L) ⟨n, hxn⟩)
  exact Module.Finite.of_injective φ hφ

-- created on 2026-10-20
