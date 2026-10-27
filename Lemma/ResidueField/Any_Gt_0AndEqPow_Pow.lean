import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing Polynomial
open ValuationSubring


private lemma exists_primitive_annihilator
  {K : Type*}
  [Field K]
  [CharZero K]
  (A : ValuationSubring K)
  (p : ℕ)
  [Fact p.Prime]
  [CharP (ResidueField A) p]
  [Algebra.IsAlgebraic ℤ K] (a : A) :
  ∃ F : ℤ[X], (∃ i, ¬ (p : ℤ) ∣ F.coeff i) ∧ aeval a F = 0 := by
  obtain ⟨F, hF0, hFa⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (a : K)
  refine ⟨F.primPart, ?_, ?_⟩
  ·
    by_contra h
    push Not at h
    have hdvd : C (p : ℤ) ∣ F.primPart := by
      rwa [C_dvd_iff_dvd_coeff]
    have hu : IsUnit (p : ℤ) :=
      (isPrimitive_iff_isUnit_of_C_dvd.mp F.isPrimitive_primPart) _ hdvd
    have hp : (p : ℤ).natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hu
    simp only [Int.natAbs_natCast] at hp
    exact (Fact.out : p.Prime).one_lt.ne' hp
  ·
    have hK : aeval (a : K) F.primPart = 0 := by
    have h := hFa
    rw [F.eq_C_content_mul_primPart, map_mul, aeval_C, mul_eq_zero] at h
    obtain h | h := h
    ·
      exfalso
      have hc : F.content ≠ 0 := fun hc => hF0 (content_eq_zero_iff.mp hc)
      rw [eq_intCast, Int.cast_eq_zero] at h
      exact hc h
    · exact h
    have h2 : (aeval (a : K) F.primPart) = ((aeval a F.primPart : A) : K) :=
      aeval_algHom_apply (IsScalarTower.toAlgHom ℤ A K) a F.primPart
    rw [h2] at hK
    exact_mod_cast hK

private lemma exists_pow_prime_pow_eq
  {K : Type*}
  [Field K]
  [CharZero K]
  (A : ValuationSubring K)
  (p : ℕ)
  [Fact p.Prime]
  [CharP (ResidueField A) p]
  [Algebra.IsAlgebraic ℤ K] (x : ResidueField A) :
  ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x := by
  classical
  obtain ⟨a, rfl⟩ := residue_surjective x
  obtain ⟨F, ⟨i, hi⟩, hFa⟩ := exists_primitive_annihilator A p a
  set G : (ResidueField A)[X] := F.map (Int.castRingHom (ResidueField A)) with hG
  have hG0 : G ≠ 0 := by
    intro h
    have hc : G.coeff i = 0 := by rw [h, coeff_zero]
    rw [hG, coeff_map, eq_intCast, CharP.intCast_eq_zero_iff (ResidueField A) p] at hc
    exact hi hc
  have hroot : ∀ m : ℕ, G.IsRoot (residue A a ^ p ^ m) := by
    intro m
    have h0 : G.eval (residue A a) = 0 := by
      have h1 : aeval (residue A a) F = residue A (aeval a F) :=
        aeval_algHom_apply ((residue A).toIntAlgHom) a F
      have hint : (algebraMap ℤ (ResidueField A)) = Int.castRingHom _ := RingHom.ext_int _ _
      rwa [hFa, map_zero, aeval_def, hint, ← eval_map] at h1
    have hfix : G.map ((frobenius (ResidueField A) p) ^ m) = G := by
      rw [hG, Polynomial.map_map]
      congr 1
      exact RingHom.ext_int _ _
    rw [IsRoot, ← iterate_frobenius, ← RingHom.coe_pow, ← hfix, eval_map, eval₂_hom, h0,
      map_zero]
  have hfin : Finite (G.roots.toFinset : Set (ResidueField A)) := Finite.of_fintype _
  let f : ℕ → (G.roots.toFinset : Set (ResidueField A)) := fun m =>
    ⟨residue A a ^ p ^ m, by
      simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hG0]
      exact hroot m⟩
  obtain ⟨m₁, m₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have heq' : residue A a ^ p ^ m₁ = residue A a ^ p ^ m₂ := congrArg Subtype.val heq
  wlog hlt : m₁ < m₂ generalizing m₁ m₂
  · exact this m₂ m₁ hne.symm heq.symm heq'.symm (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)
  refine ⟨m₂ - m₁, Nat.sub_pos_of_lt hlt, ?_⟩
  have hinj : Function.Injective ((frobenius (ResidueField A) p)^[m₁]) :=
    (frobenius_inj (ResidueField A) p).iterate m₁
  refine hinj
  rw [iterate_frobenius, iterate_frobenius, ← pow_mul, ← pow_add, Nat.sub_add_cancel hlt.le]
  apply heq'.symm
/--
[ValuationSubring_exists_pow_prime_pow_eq_self_of_isAlgebraic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_pow_prime_pow_eq_self_of_isAlgebraic.lean)
-/
@[path]
private lemma main
  [Field K] [CharZero K] [Algebra.IsAlgebraic ℤ K]
  {A : ValuationSubring K}
  {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
  {x : IsLocalRing.ResidueField A} :
-- imply
  ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x :=
-- proof
  exists_pow_prime_pow_eq A p x


-- created on 2026-10-23
