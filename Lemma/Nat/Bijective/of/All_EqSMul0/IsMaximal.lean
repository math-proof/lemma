import Mathlib
import sympy.Basic


/--
[Module_bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot.lean)
-/
@[path]
private lemma main
  [CommRing T] [AddCommGroup M] [Module T M]
  {𝔓 : Ideal T}
  {k : ℕ}
  {u : T}
-- given
  (h𝔓 : 𝔓.IsMaximal)
  (hk : ∀ (a : T), a ∈ 𝔓 ^ k → ∀ x : M, a • x = 0)
  (hu : u ∉ 𝔓) :
-- imply
  Function.Bijective (fun x : M => u • x) := by
-- proof
  classical

  have hfield := (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔓).mp h𝔓
  obtain ⟨v, hv⟩ : ∃ v : T, 1 - u * v ∈ 𝔓 := by
    have hne : (Ideal.Quotient.mk 𝔓 u) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨w, hw⟩ := hfield.mul_inv_cancel hne
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine ⟨v, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, hw, sub_self]

  set x : T := 1 - u * v with hx
  have hxk : x ^ k ∈ 𝔓 ^ k := Ideal.pow_mem_pow hv k
  have hgeom : (1 - x) * (Finset.range k).sum (fun i => x ^ i) = 1 - x ^ k := mul_neg_geom_sum x k
  set w : T := v * (Finset.range k).sum (fun i => x ^ i) with hw
  have huw : u * w = 1 - x ^ k := by
    rw [hw, ← mul_assoc, ← hgeom]
    congr 1
    rw [hx]; ring

  have hinv : ∀ y : M, u • (w • y) = y ∧ w • (u • y) = y := by
    intro y
    have h1 : (u * w) • y = y := by
      rw [huw, sub_smul, one_smul, hk _ hxk, sub_zero]
    constructor
    · rw [← mul_smul, h1]
    · rw [← mul_smul, mul_comm, h1]
  refine ⟨fun a b hab => ?_, fun y => ⟨w • y, (hinv y).1⟩⟩
  have := congrArg (fun z => w • z) hab
  simp only at this
  rwa [(hinv a).2, (hinv b).2] at this


-- created on 2026-10-05
