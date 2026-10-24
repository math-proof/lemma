import Mathlib

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure TowerQuotientDatum
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] (a : ∀ n : ℕ, G →* Aut (X n)) : Type 1 where

  Y : ℕ → Scheme.{0}

  yb : ∀ n : ℕ, Y n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))

  yt : ∀ n : ℕ, Y n ⟶ Y (n + 1)

  yt_isPullback : ∀ n : ℕ, IsPullback (yt n) (yb n) (yb (n + 1))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))))

  yb_isProper : ∀ n : ℕ, IsProper (yb n)

  yb_flat : ∀ n : ℕ, Flat (yb n)

  p : ∀ n : ℕ, X n ⟶ Y n

  p_over : ∀ n : ℕ, p n ≫ yb n = xb n

  p_xt : ∀ n : ℕ, xt n ≫ p (n + 1) = p n ≫ yt n

  p_isPullback : ∀ n : ℕ, IsPullback (xt n) (p n) (p (n + 1)) (yt n)

  p_inv : ∀ (n : ℕ) (g : G), (a n g).hom ≫ p n = p n

  p_isFinite : ∀ n : ℕ, IsFinite (p n)

  p_surjective : ∀ n : ℕ, Surjective (p n)

  p_epi_loc : ∀ (n : ℕ) (U : (Y n).Opens), Epi ((p n) ∣_ U)

  univ_loc : ∀ (T : Scheme.{0}) (U : ∀ n : ℕ, (Y n).Opens) (hU : ∀ n : ℕ, (yt n) ⁻¹ᵁ (U (n + 1)) = U n)
    (u : ∀ n : ℕ, (↑((p n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T),
    (∀ (n : ℕ) (g : G),
      Scheme.Hom.resLE (a n g).hom ((p n) ⁻¹ᵁ (U n)) ((p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, p_inv]) ≫ u n = u n) →
    (∀ n : ℕ,
      Scheme.Hom.resLE (xt n) ((p (n + 1)) ⁻¹ᵁ (U (n + 1))) ((p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, p_xt, Scheme.Hom.comp_preimage, hU]) ≫ u (n + 1) = u n) →
    ∃ v : ∀ n : ℕ, (↑(U n) : Scheme.{0}) ⟶ T, ∀ n : ℕ, (p n) ∣_ (U n) ≫ v n = u n

  fib : ∀ (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] (y : Spec (CommRingCat.of k) ⟶ Y n),
    (∃ x : Spec (CommRingCat.of k) ⟶ X n, x ≫ p n = y) ∧
    ∀ x x' : Spec (CommRingCat.of k) ⟶ X n, x ≫ p n = y → (x' ≫ p n = y ↔ ∃ g : G, x' = x ≫ (a n g).hom)

  adicFib : ∀ (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra 𝒪 R],
    IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R → IsAlgClosed (FractionRing R) →
    ∀ (y : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)})) ⟶ Y n),
    (∀ n : ℕ, y n ≫ yb n = Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)}) (algebraMap 𝒪 R)
      (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))) →
    (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ y (n + 1) = y n ≫ yt n) →
    (∃ x : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)})) ⟶ X n,
      (∀ n : ℕ, x n ≫ p n = y n) ∧
      ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ x (n + 1) = x n ≫ xt n) ∧
    ∀ x x' : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)})) ⟶ X n,
      (∀ n : ℕ, x n ≫ p n = y n) → (∀ n : ℕ, x' n ≫ p n = y n) →
      (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ x (n + 1) = x n ≫ xt n) →
      (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ x' (n + 1) = x' n ≫ xt n) →
      ∃ g : G, ∀ n : ℕ, x' n = x n ≫ (a n g).hom

end AlgebraicGeometry
