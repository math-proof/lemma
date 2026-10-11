import Mathlib
import sympy.Basic


/--
[AlgHom_range_eq_range_aeval_X_of_isIntegral_adjoin_singleton](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_range_eq_range_aeval_X_of_isIntegral_adjoin_singleton.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {B : Type v} [CommRing B] [Algebra k B]
  {b₀ : B}
  {ψ : B →ₐ[k] RatFunc k}
-- given
  (hint : ∀ b : B, IsIntegral ↥(Algebra.adjoin k ({b₀} : Set B)) b)
  (hψ : ψ b₀ = RatFunc.X) :
-- imply
  ψ.range = (Polynomial.aeval (RatFunc.X : RatFunc k)).range := by
-- proof
  classical

    have haev : ∀ q : Polynomial k,
        Polynomial.aeval (RatFunc.X : RatFunc k) q = algebraMap (Polynomial k) (RatFunc k) q := by
      intro q
      rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
    apply le_antisymm
    · rintro _ ⟨b, rfl⟩

      obtain ⟨P, hPm, hPb⟩ := hint b
      have hlift : P.map (ψ.toRingHom.comp (algebraMap ↥(Algebra.adjoin k ({b₀} : Set B)) B)) ∈
          Polynomial.lifts (algebraMap (Polynomial k) (RatFunc k)) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        rw [Polynomial.coeff_map]
        have hmem : ψ ((P.coeff n : ↥(Algebra.adjoin k ({b₀} : Set B))) : B) ∈
            (Algebra.adjoin k ({b₀} : Set B)).map ψ :=
          Subalgebra.mem_map.mpr ⟨_, (P.coeff n).2, rfl⟩
        rw [AlgHom.map_adjoin, Set.image_singleton, hψ, Algebra.adjoin_singleton_eq_range_aeval] at hmem
        obtain ⟨q, hq⟩ := (AlgHom.mem_range _).mp hmem
        exact ⟨q, (haev q).symm.trans hq⟩
      obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift (hPm.map _)
      have hI : IsIntegral (Polynomial k) (ψ b) := by
        refine ⟨Q, hQm, ?_⟩
        rw [← Polynomial.eval_map, hQmap, Polynomial.eval_map]
        exact (Polynomial.hom_eval₂ P (algebraMap ↥(Algebra.adjoin k ({b₀} : Set B)) B) ψ.toRingHom b).symm.trans
          (by rw [hPb, map_zero])
      obtain ⟨q, hq⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Polynomial k) (K := RatFunc k)).mp hI
      exact (AlgHom.mem_range _).mpr ⟨q, (haev q).trans hq⟩
    · rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr ⟨b₀, hψ⟩)


-- created on 2026-10-10
