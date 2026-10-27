import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma eq_zero_of_forall_mem_span_pow {p : ℕ} [Fact p.Prime] (z : ℤ_[p]) (hz : ∀ k : ℕ, z ∈ Ideal.span {(p : ℤ_[p]) ^ k}) : z = 0 := by
  by_contra hne
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h1 : ‖z‖ ≤ (p : ℝ) ^ (-((z.valuation + 1 : ℕ) : ℤ)) := (PadicInt.norm_le_pow_iff_mem_span_pow z _).mpr (hz _)
  rw [PadicInt.norm_eq_zpow_neg_valuation hne, zpow_le_zpow_iff_right₀ hp] at h1
  push_cast at h1
  omega
private lemma apply_eq_smul_apply_one {p : ℕ} [Fact p.Prime] {M : Type v} [AddCommGroup M] [Module ℤ_[p] M] [Module.Free ℤ_[p] M] (g : ℤ_[p] →+ M) (c : ℤ_[p]) : g c = c • g 1 := by
  let h : ℤ_[p] →+ M := g - (AddMonoidHom.mk' (fun a : ℤ_[p] => a • g 1) (fun a b => add_smul a b _))
  have hh : ∀ a : ℤ_[p], h a = g a - a • g 1 := fun a => rfl
  have h_nat : ∀ n : ℕ, h (n : ℤ_[p]) = 0 := by
    intro n
    rw [hh, sub_eq_zero, ← nsmul_one, map_nsmul, nsmul_one, Nat.cast_smul_eq_nsmul]
  have hk : ∀ k : ℕ, ∃ m : M, h c = ((p : ℤ_[p]) ^ k) • m := by
    intro k
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec k c)
    refine ⟨h d, ?_⟩
    have hc : c = (c.appr k : ℤ_[p]) + ((p ^ k : ℕ) : ℤ_[p]) * d := by
      push_cast
      linear_combination (-1 : ℤ_[p]) * hd
    rw [hc, map_add, h_nat, zero_add, ← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p]]
    push_cast
    rfl
  suffices h0 : h c = 0 by
    rw [hh] at h0
    apply sub_eq_zero.mp h0
  let b := Module.Free.chooseBasis ℤ_[p] M
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  apply eq_zero_of_forall_mem_span_pow
  intro k
  obtain ⟨m, hm⟩ := hk k
  rw [hm, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  refine Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
/--
[PadicInt_addMonoidHom_map_smul_of_free](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PadicInt_addMonoidHom_map_smul_of_free.lean)
-/
@[path]
private lemma main
  (p : ℕ) [Fact p.Prime]
  {N : Type u} [AddCommGroup N] [Module ℤ_[p] N] [Module.Free ℤ_[p] N]
  {M : Type v} [AddCommGroup M] [Module ℤ_[p] M] [Module.Free ℤ_[p] M]
  (f : N →+ M) (c : ℤ_[p]) (x : N) :
  -- imply
  f (c • x) = c • f x := by
  -- proof
  let b := Module.Free.chooseBasis ℤ_[p] N
  have key : ∀ (i : Module.Free.ChooseBasisIndex ℤ_[p] N) (a : ℤ_[p]), f (a • b i) = a • f (b i) := by
    intro i a
    have := apply_eq_smul_apply_one (AddMonoidHom.mk' (fun a : ℤ_[p] => f (a • b i)) (fun a a' => by simp only [add_smul, map_add])) a
    simpa using this
  conv_lhs => rw [← b.linearCombination_repr x]
  conv_rhs => rw [← b.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.smul_sum, map_finsuppSum, map_finsuppSum, Finsupp.smul_sum]
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, key, key, smul_smul]


-- created on 2026-10-20
