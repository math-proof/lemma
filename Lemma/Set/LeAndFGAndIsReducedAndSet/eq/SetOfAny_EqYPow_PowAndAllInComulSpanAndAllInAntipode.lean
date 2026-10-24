import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] [PerfectField k]
  {p : ℕ} [Fact p.Prime] [CharP k p]
  {H : Type v} [CommRing H] [HopfAlgebra k H]
  {K : Subalgebra k H}
  -- given
  (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
  (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
  (hfg : K.FG) :
  -- imply
  ∃ (r : ℕ) (K' : Subalgebra k H), K' ≤ K ∧ K'.FG ∧ IsReduced ↥K' ∧ (K' : Set H) = {y : H | ∃ x ∈ K, y = x ^ p ^ r} ∧ (∀ x ∈ K', Coalgebra.comul (R := k) x ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b}) ∧ (∀ x ∈ K', HopfAlgebra.antipode k x ∈ K') := by
  -- proof
  classical
  have hp : p.Prime := Fact.out
  let _ : Algebra.FiniteType k ↥K := ⟨Iff.mpr (Subalgebra.fg_top K) hfg⟩
  let _ : IsNoetherianRing ↥K := Algebra.FiniteType.isNoetherianRing k ↥K
  obtain ⟨m, hm⟩ := IsNoetherianRing.isNilpotent_nilradical ↥K
  obtain ⟨r, hr⟩ : ∃ r : ℕ, m ≤ p ^ r := ⟨m, (Nat.lt_pow_self hp.one_lt).le⟩
  have hq0 : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero
  have hadd : ∀ x y : H, (x + y) ^ p ^ r = x ^ p ^ r + y ^ p ^ r := by
    obtain hH | hH := subsingleton_or_nontrivial H
    ·
      intro x y
      apply Subsingleton.elim _ _
    ·
      let _ : CharP H p := charP_of_injective_algebraMap (algebraMap k H).injective p
      intro x y
      apply add_pow_char_pow x y p r
  have hadd₂ : ∀ x y : H ⊗[k] H, (x + y) ^ p ^ r = x ^ p ^ r + y ^ p ^ r := by
    obtain hH | hH := subsingleton_or_nontrivial (H ⊗[k] H)
    ·
      intro x y
      apply Subsingleton.elim _ _
    ·
      let _ : CharP (H ⊗[k] H) p := charP_of_injective_algebraMap (algebraMap k (H ⊗[k] H)).injective p
      intro x y
      apply add_pow_char_pow x y p r
  have hroot' : ∀ (n : ℕ) (c : k), ∃ d : k, d ^ p ^ n = c := by
    intro n
    induction n
    ·
      intro c
      exact ⟨c, by rw [pow_zero, pow_one]⟩
    ·
      rename_i n ih
      intro c
      obtain ⟨d, hd⟩ := ih c
      obtain ⟨e, he⟩ := (bijective_frobenius k p).2 d
      rw [frobenius_def] at he
      exact ⟨e, by rw [pow_succ', pow_mul, he, hd]⟩
  have hroot : ∀ c : k, ∃ d : k, d ^ p ^ r = c := hroot' r
  have hSpow : ∀ (x : H) (n : ℕ), HopfAlgebra.antipode k (x ^ n) = (HopfAlgebra.antipode k x) ^ n := by
    intro x n
    induction n
    · rw [pow_zero, pow_zero, HopfAlgebra.antipode_one]
    ·
      rename_i n ih
      rw [pow_succ, HopfAlgebra.antipode_mul_antidistrib, ih, ← pow_succ']
  let K' : Subalgebra k H :=
    { carrier := {y : H | ∃ x ∈ K, y = x ^ p ^ r}
      mul_mem' := by
        intro y1 y2 hy1 hy2
        obtain ⟨x, hx, rfl⟩ := hy1
        obtain ⟨y, hy, rfl⟩ := hy2
        exact ⟨x * y, K.mul_mem hx hy, (mul_pow x y _).symm⟩
      one_mem' := ⟨1, K.one_mem, (one_pow _).symm⟩
      add_mem' := by
        intro y1 y2 hy1 hy2
        obtain ⟨x, hx, rfl⟩ := hy1
        obtain ⟨y, hy, rfl⟩ := hy2
        exact ⟨x + y, K.add_mem hx hy, (hadd x y).symm⟩
      zero_mem' := ⟨0, K.zero_mem, (zero_pow hq0).symm⟩
      algebraMap_mem' := fun c => by
        obtain ⟨d, hd⟩ := hroot c
        exact ⟨algebraMap k H d, K.algebraMap_mem d, by rw [← map_pow, hd]⟩ }
  have memK' : ∀ y : H, y ∈ K' ↔ ∃ x ∈ K, y = x ^ p ^ r := fun _ => Iff.rfl
  have hpowK' : ∀ x ∈ K, x ^ p ^ r ∈ K' := fun x hx => ⟨x, hx, rfl⟩
  refine ⟨r, K', ?_, ?_, ?_, rfl, ?_, ?_⟩
  ·
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply K.pow_mem hx _
  ·
    obtain ⟨t, ht⟩ := hfg
    refine ⟨t.image fun x => x ^ p ^ r, le_antisymm ?_ ?_⟩
    ·
      apply Algebra.adjoin_le
      intro y hy
      rw [Finset.coe_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      apply hpowK' x (ht ▸ Algebra.subset_adjoin hx)
    ·
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [← ht] at hx
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
      ·
        intro y hy
        apply Algebra.subset_adjoin
        rw [Finset.coe_image]
        exact ⟨y, hy, rfl⟩
      ·
        intro c
        rw [← map_pow]
        apply Subalgebra.algebraMap_mem _ _
      ·
        intro y z _ _ hy hz
        rw [hadd]
        apply Subalgebra.add_mem _ hy hz
      ·
        intro y z _ _ hy hz
        rw [mul_pow]
        apply Subalgebra.mul_mem _ hy hz
  ·
    refine ⟨fun y hy => ?_⟩
    obtain ⟨n, hn⟩ := hy
    obtain ⟨x, hx, hxq⟩ := Iff.mp (memK' y) y.2
    have hyn : (y : H) ^ n = 0 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hxn : (⟨x, hx⟩ : ↥K) ∈ nilradical ↥K := by
      refine ⟨p ^ r * n, Subtype.ext ?_⟩
      show x ^ (p ^ r * n) = 0
      rw [pow_mul, ← hxq]
      apply hyn
    have hxm : x ^ m = 0 := by
      have h1 := Ideal.pow_mem_pow hxn m
      rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at h1
      simpa using congrArg Subtype.val h1
    apply Subtype.ext
    show (y : H) = 0
    rw [hxq, ← Nat.add_sub_cancel' hr, pow_add, hxm, zero_mul]
  ·
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hpow : ∀ t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}, t ^ p ^ r ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b} := by
      intro t ht
      refine Submodule.span_induction ?_ ?_ ?_ ?_ ht
      ·
        intro s hs
        obtain ⟨a, ha, b, hb, rfl⟩ := hs
        rw [Algebra.TensorProduct.tmul_pow]
        apply Submodule.subset_span
          (⟨a ^ p ^ r, hpowK' a ha, b ^ p ^ r, hpowK' b hb, rfl⟩ :
            (a ^ p ^ r) ⊗ₜ[k] (b ^ p ^ r) ∈
              {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b})
      ·
        rw [zero_pow hq0]
        apply Submodule.zero_mem _
      ·
        intro s t _ _ hs ht
        rw [hadd₂]
        apply Submodule.add_mem _ hs ht
      ·
        intro c s _ hs
        rw [smul_pow]
        apply Submodule.smul_mem _ _ hs
    rw [show Coalgebra.comul (R := k) (x ^ p ^ r) = (Coalgebra.comul (R := k) x) ^ p ^ r by rw [← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply]]
    apply hpow _ (hΔ x hx)
  ·
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hSpow]
    apply hpowK' _ (hS x hx)


-- created on 2026-10-20
