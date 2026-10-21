import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[Polynomial_aeval_notMem_of_height_eq_one_of_map_residue_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_aeval_notMem_of_height_eq_one_of_map_residue_ne_zero.lean)
-/
@[path]
private lemma main
    {A C : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing C] [IsDomain C] [Algebra A C]
    (x : C) (hx : Function.Injective (Polynomial.aeval (R := A) x))
    (hint : (Polynomial.aeval (R := A) x).toRingHom.IsIntegral)
    (Q : Ideal C) [Q.IsPrime] (hQ : Q.height = 1)
    (hQm : (IsLocalRing.maximalIdeal A).map (algebraMap A C) ≤ Q)
    (P : Polynomial A) (hP : P.map (IsLocalRing.residue A) ≠ 0) :
    Polynomial.aeval x P ∉ Q := by
  classical
  intro hmem
  let alg : Algebra (Polynomial A) C := (Polynomial.aeval (R := A) x).toRingHom.toAlgebra
  have halg : ∀ q : Polynomial A, algebraMap (Polynomial A) C q = Polynomial.aeval x q := fun _ => rfl
  let _ : Algebra.IsIntegral (Polynomial A) C := ⟨hint⟩
  let _ : Module.IsTorsionFree (Polynomial A) C := Module.isTorsionFree_iff_algebraMap_injective.mpr hx
  let q : Ideal (Polynomial A) := Q.comap (algebraMap (Polynomial A) C)
  let q₀ : Ideal (Polynomial A) := (IsLocalRing.maximalIdeal A).map Polynomial.C
  let hq₀ : q₀.IsPrime := Ideal.isPrime_map_C_of_isPrime
  let hq : q.IsPrime := Ideal.IsPrime.comap _
  have hq₀q : q₀ ≤ q := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    show algebraMap (Polynomial A) C (Polynomial.C a) ∈ Q
    rw [halg, Polynomial.aeval_C]
    exact hQm (Ideal.mem_map_of_mem _ ha)
  have hPq : P ∈ q := hmem
  have hPq₀ : P ∉ q₀ := by
    intro h
    apply hP
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff]
    exact Ideal.mem_map_C_iff.mp h n
  have hlt : q₀ < q := lt_of_le_of_ne hq₀q (fun h => hPq₀ (h ▸ hPq))
  have hq₀ne : q₀ ≠ ⊥ := by
    intro h0
    exact IsDiscreteValuationRing.not_a_field A
      ((Ideal.map_eq_bot_iff_of_injective Polynomial.C_injective).mp h0)
  let hbp : (⊥ : Ideal (Polynomial A)).IsPrime := Ideal.isPrime_bot
  have hbot : (⊥ : Ideal (Polynomial A)) < q₀ := bot_lt_iff_ne_bot.mpr hq₀ne
  let _ : Q.LiesOver q := ⟨rfl⟩
  obtain ⟨Q₀, hQ₀Q, hQ₀p, hQ₀over⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := q₀) (q := q) Q hlt
  let _ := hQ₀p
  let _ := hQ₀over
  obtain ⟨Q', hQ'Q₀, -, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := q₀) Q₀ hbot
  have hQ₀ne : Q₀.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff]
    exact ne_bot_of_gt hQ'Q₀
  have h1 : Q.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hQ]; exact_mod_cast le_rfl
  have hlt' := (Ideal.height_le_iff.mp h1) Q₀ hQ₀p hQ₀Q
  exact hQ₀ne (ENat.lt_one_iff_eq_zero.mp (by exact_mod_cast hlt'))

-- created on 2026-10-20
