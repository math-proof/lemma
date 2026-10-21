import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
private lemma smodEq_pow_smul_top_iff (I : Ideal R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
private lemma isAdicComplete_map_of_surjective [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : R →+* S)
    (hf : Function.Surjective f) : IsAdicComplete (I.map f) S := by
  have hI : I ≤ (⊥ : Ideal R).jacobson := IsAdicComplete.le_jacobson_bot I
  let _ : IsNoetherianRing S := isNoetherianRing_of_surjective R S f hf
  have hJ : I.map f ≤ (⊥ : Ideal S).jacobson := by
    intro x hx
    rw [Ideal.mem_map_iff_of_surjective f hf] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨b, rfl⟩ := hf y
    have hu := Ideal.mem_jacobson_bot.mp (hI ha) b
    simpa using hu.map f
  let hH : IsHausdorff (I.map f) S := IsHausdorff.of_le_jacobson _ _ hJ
  have hP : IsPrecomplete (I.map f) S := by
    refine ⟨fun g hg => ?_⟩
    have hdiff : ∀ n, ∃ d : R, d ∈ I ^ n ∧ f d = g (n + 1) - g n := by
      intro n
      have h := (smodEq_pow_smul_top_iff _ _ _ _).mp (hg (Nat.le_succ n)).symm
      rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective f hf] at h
      exact h
    choose d hdI hdf using hdiff
    obtain ⟨r₀, hr₀⟩ := hf (g 0)
    let r : ℕ → R := fun n => Nat.rec r₀ (fun k acc => acc + d k) n
    have hr_succ : ∀ n, r (n + 1) = r n + d n := fun n => rfl
    have hfr : ∀ n, f (r n) = g n := by
      intro n
      induction n with
      | zero => exact hr₀
      | succ k ih => rw [hr_succ, map_add, ih, hdf]; ring
    have hcauchy : ∀ m n, m ≤ n → r n - r m ∈ I ^ m := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ k hmk ih =>
        rw [hr_succ, show r k + d k - r m = (r k - r m) + d k by ring]
        exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right hmk (hdI k))
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I R) (f := r)
      (fun {m n} hmn => by
        rw [smodEq_pow_smul_top_iff]
        have := hcauchy m n hmn
        rwa [← neg_sub, Ideal.neg_mem_iff])
    refine ⟨f L, fun n => ?_⟩
    rw [smodEq_pow_smul_top_iff, ← hfr n, ← map_sub, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ((smodEq_pow_smul_top_iff _ _ _ _).mp (hL n))
  exact ⟨⟩
private lemma isAdicComplete_map_maximalIdeal_quotient [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (J : Ideal R) :
    IsAdicComplete ((maximalIdeal R).map (Ideal.Quotient.mk J)) (R ⧸ J) :=
  isAdicComplete_map_of_surjective _ _ Ideal.Quotient.mk_surjective
/--
[IsAdicComplete_map_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsAdicComplete_map_of_surjective.lean)
-/
@[path]
private lemma main {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R →+* S) (hf : Function.Surjective f) : IsAdicComplete (I.map f) S :=
  isAdicComplete_map_of_surjective I f hf

-- created on 2026-10-20
