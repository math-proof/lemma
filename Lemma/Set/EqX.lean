import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental.lean)
-/
@[path]
private lemma main
  (K : Type u) [Field K]
  (L : Type v) [Field L] [Algebra K L]
  (x : L) (hx : Transcendental K x) :
  -- imply
  ∃ e : AlgEquiv K ↥(IntermediateField.adjoin K ({x} : Set L)) (RatFunc K), e ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ = RatFunc.X := by
  -- proof
  classical
  have hinj0 : Function.Injective (Polynomial.aeval (R := K) x) := transcendental_iff_injective.mp hx
  have hφ : nonZeroDivisors (Polynomial K) ≤ Submonoid.comap (Polynomial.aeval x : AlgHom K (Polynomial K) L) (nonZeroDivisors L) := by
    intro p hp
    apply mem_nonZeroDivisors_of_ne_zero (fun h => nonZeroDivisors.ne_zero hp (hinj0 (h.trans (map_zero _).symm)))
  let ψ : AlgHom K (RatFunc K) L := RatFunc.liftAlgHom (Polynomial.aeval x) hφ
  have hψ : ∀ p q : Polynomial K, ψ (algebraMap _ (RatFunc K) p / algebraMap _ (RatFunc K) q) = Polynomial.aeval x p / Polynomial.aeval x q := RatFunc.liftAlgHom_apply_div _ hφ
  have hmemA : ∀ p : Polynomial K, Polynomial.aeval x p ∈ IntermediateField.adjoin K ({x} : Set L) := fun p => by
    apply IntermediateField.algebra_adjoin_le_adjoin K _
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    refine ⟨p, rfl⟩
  have hrange : ∀ r : RatFunc K, ψ r ∈ IntermediateField.adjoin K ({x} : Set L) := by
    intro r
    rw [← RatFunc.num_div_denom r, hψ]
    apply div_mem (hmemA _) (hmemA _)
  let f : AlgHom K (RatFunc K) ↥(IntermediateField.adjoin K ({x} : Set L)) := ψ.codRestrict (IntermediateField.adjoin K ({x} : Set L)).toSubalgebra hrange
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => (ψ : RingHom (RatFunc K) L).injective (congrArg (fun z : ↥(IntermediateField.adjoin K ({x} : Set L)) => (z : L)) h), fun y => ?_⟩
    obtain ⟨r, hr, s, hs, hy⟩ := IntermediateField.mem_adjoin_iff_div.mp y.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr hs
    obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hr
    obtain ⟨q, rfl⟩ := (AlgHom.mem_range _).mp hs
    refine ⟨algebraMap _ (RatFunc K) p / algebraMap _ (RatFunc K) q, Subtype.ext ?_⟩
    change ψ (algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q) = (y : L)
    rw [hψ, ← hy]
  refine ⟨(AlgEquiv.ofBijective f hf).symm, ?_⟩
  rw [AlgEquiv.symm_apply_eq, AlgEquiv.ofBijective_apply]
  apply Subtype.ext
  change x = ψ RatFunc.X
  rw [← RatFunc.algebraMap_X, ← div_one (algebraMap (Polynomial K) (RatFunc K) Polynomial.X), ← map_one (algebraMap (Polynomial K) (RatFunc K)), hψ, map_one, div_one, Polynomial.aeval_X]


-- created on 2026-10-20
