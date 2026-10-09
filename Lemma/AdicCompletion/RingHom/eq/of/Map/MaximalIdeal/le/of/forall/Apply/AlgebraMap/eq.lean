import sympy.Basic
import Mathlib

open IsLocalRing
set_option maxHeartbeats 800000

/-! Port of FLT Def_AdicCompletionLocalRing (Kernel: maximalIdeal_fg / exists_eq_algebraMap_add). -/
namespace AdicCompletion

variable {A : Type*} [CommRing A]

theorem evalₐ_algebraMap (I : Ideal A) (n : ℕ) (a : A) :
    evalₐ I n (algebraMap A (AdicCompletion I A) a) = Ideal.Quotient.mk _ a := by
  rw [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, evalₐ_of]

theorem mem_ker_evalₐ_iff (I : Ideal A) (n : ℕ) (x : AdicCompletion I A) :
    x ∈ RingHom.ker (evalₐ I n) ↔ x ∈ LinearMap.ker (eval I A n) := by
  have h : (I ^ n • ⊤ : Ideal A) = I ^ n := by rw [smul_eq_mul, Ideal.mul_top]
  rw [RingHom.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx; rw [← factor_evalₐ_eq_eval I x h.ge, hx]; exact RingHom.map_zero _
  · intro hx; rw [← factor_eval_eq_evalₐ I x h.le, hx]; exact LinearMap.map_zero _

theorem ker_evalₐ_eq_map_pow (I : Ideal A) (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  ext x
  rw [mem_ker_evalₐ_iff, ← pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map,
    Submodule.restrictScalars_mem]

theorem exists_eq_algebraMap_add (I : Ideal A) (hI : I.FG) (n : ℕ) (x : AdicCompletion I A) :
    ∃ a : A, ∃ y : AdicCompletion I A,
      ∃ _hy : y ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)),
        algebraMap A (AdicCompletion I A) a + y = x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  refine ⟨a, x - algebraMap A _ a, ?_, by ring⟩
  rw [← ker_evalₐ_eq_map_pow I hI, RingHom.mem_ker, map_sub, evalₐ_algebraMap, ha, sub_self]

theorem maximalIdeal_fg {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    (maximalIdeal A).FG := IsNoetherian.noetherian _

end AdicCompletion

/--
[AdicCompletion_ringHom_eq_of_map_maximalIdeal_le_of_forall_apply_algebraMap_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_ringHom_eq_of_map_maximalIdeal_le_of_forall_apply_algebraMap_eq.lean)
-/
@[path]
private lemma main
  {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {T : Type*} [CommRing T] [IsLocalRing T] [IsHausdorff (maximalIdeal T) T]
-- given
  (g₁ g₂ : AdicCompletion (maximalIdeal R) R →+* T) (hg₁ : ∀ x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R), g₁ x ∈ maximalIdeal T) (hg₂ : ∀ x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R), g₂ x ∈ maximalIdeal T) (h : ∀ r : R, g₁ (algebraMap R (AdicCompletion (maximalIdeal R) R) r) =
      g₂ (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) :
-- imply
  g₁ = g₂ := by
-- proof
  apply RingHom.ext
  intro x
  have hmap : ∀ (g : AdicCompletion (maximalIdeal R) R →+* T),
      (∀ y ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R), g y ∈ maximalIdeal T) →
      ∀ (n : ℕ) (y : AdicCompletion (maximalIdeal R) R),
        y ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n → g y ∈ maximalIdeal T ^ n := by
    intro g hg n y hy
    have hle : (maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n).map g ≤ maximalIdeal T ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun z hz => Ideal.mem_comap.mpr (hg z hz)) n
    exact hle (Ideal.mem_map_of_mem g hy)
  have key : ∀ n : ℕ, g₁ x - g₂ x ∈ maximalIdeal T ^ n := by
    intro n
    obtain ⟨a, y, hy, rfl⟩ :=
      AdicCompletion.exists_eq_algebraMap_add (maximalIdeal R) (AdicCompletion.maximalIdeal_fg (A := R)) n x
    have hy' : y ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]; exact hy
    have e : g₁ (algebraMap R _ a + y) - g₂ (algebraMap R _ a + y) = g₁ y - g₂ y := by
      rw [map_add, map_add, h a]; ring
    rw [e]
    exact Ideal.sub_mem _ (hmap g₁ hg₁ n y hy') (hmap g₂ hg₂ n y hy')
  have hz : g₁ x - g₂ x = 0 := by
    refine IsHausdorff.haus ‹IsHausdorff (maximalIdeal T) T› _ fun n => ?_
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact key n
  exact sub_eq_zero.mp hz

-- created on 2026-10-09
