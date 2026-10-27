import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing


/--
[AlgebraicCurve_mem_of_mul_eval2_mem_of_forall_coeff_mem_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_mem_of_mul_eval2_mem_of_forall_coeff_mem_maximalIdeal.lean)
-/
@[path]
private lemma main
  [Field L] [IsAlgClosed L] [Field F] [Algebra L F]
  {A : ValuationSubring L} {S : Subring F} {T f : F} {P : Polynomial ↥A}
-- given
  (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S) (hT : T ∈ S)
  (hP : P.Monic) (hPc : ∀ i : ℕ, i < P.natDegree → P.coeff i ∈ maximalIdeal ↥A)
  (hfP : f * Polynomial.eval₂ ((algebraMap L F).comp (algebraMap ↥A L)) T P ∈ S)
  (hc : ∀ c : ↥A, c ∈ maximalIdeal ↥A →
    ∃ O : Subring F, S ≤ O ∧ f ∈ O ∧ ∀ u : F, u ∈ O → u * (T - algebraMap L F (c : L)) ∈ S → u ∈ S) :
-- imply
  f ∈ S := by
-- proof
  classical
  set ι : ↥A →+* F := (algebraMap L F).comp (algebraMap ↥A L) with hι
  have hιa : ∀ a : ↥A, ι a = algebraMap L F (a : L) := fun a => rfl
  set PL : Polynomial L := P.map (algebraMap ↥A L) with hPL
  have hPLm : PL.Monic := hP.map _
  have hcard : PL.roots.card = PL.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod : (PL.roots.map fun a => Polynomial.X - Polynomial.C a).prod = PL :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPLm hcard
  have hroots : ∀ r ∈ PL.roots, ∃ c : ↥A, c ∈ maximalIdeal ↥A ∧ (c : L) = r := by
    intro r hr
    have hr0 : PL.eval r = 0 := (Polynomial.mem_roots hPLm.ne_zero).mp hr |>.eq_zero
    have hint : IsIntegral ↥A r := ⟨P, hP, by rwa [Polynomial.eval_map] at hr0⟩
    obtain ⟨c, hc⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := L)).mp hint
    refine ⟨c, ?_, hc⟩
    have hPc0 : P.eval c = 0 := by
      have h1 : algebraMap ↥A L (P.eval c) = 0 := by
        rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map, hc]
        apply hr0
      refine (map_eq_zero_iff _ (IsFractionRing.injective ↥A L)).mp h1
    have hsum := Polynomial.eval_eq_sum_range (p := P) c
    rw [Finset.sum_range_succ, hP.coeff_natDegree, one_mul, hPc0] at hsum
    have hpow : c ^ P.natDegree ∈ maximalIdeal ↥A := by
      have : c ^ P.natDegree = -∑ i ∈ Finset.range P.natDegree, P.coeff i * c ^ i := by
        linear_combination -hsum
      rw [this]
      exact Submodule.neg_mem _ (Ideal.sum_mem _ fun i hi =>
        Ideal.mul_mem_right _ _ (hPc i (Finset.mem_range.mp hi)))
    refine Ideal.IsPrime.mem_of_pow_mem inferInstance _ hpow
  have heval : Polynomial.eval₂ ι T P = (PL.roots.map fun r => T - algebraMap L F r).prod := by
    rw [Polynomial.eval₂_eq_eval_map]
    have : P.map ι = ((PL.roots.map fun a => Polynomial.X - Polynomial.C a).prod).map (algebraMap L F) := by
      rw [hprod, hPL, Polynomial.map_map]
    rw [this, Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod, Multiset.map_map,
      Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simp
  rw [heval] at hfP
  suffices key : ∀ m : Multiset L, (∀ r ∈ m, ∃ c : ↥A, c ∈ maximalIdeal ↥A ∧ (c : L) = r) →
      f * (m.map fun r => T - algebraMap L F r).prod ∈ S → f ∈ S from
    key PL.roots hroots hfP
  intro m
  refine Multiset.induction_on m ?_ ?_
  ·
    intro _ h1
    simpa using h1
  ·
    intro r m ih hm hfm
    obtain ⟨c, hcm, hcr⟩ := hm r (Multiset.mem_cons_self r m)
    obtain ⟨O, hSO, hfO, hcancel⟩ := hc c hcm
    have hm' : ∀ r' ∈ m, ∃ c : ↥A, c ∈ maximalIdeal ↥A ∧ (c : L) = r' :=
      fun r' hr' => hm r' (Multiset.mem_cons_of_mem hr')
    have hprodS : (m.map fun r => T - algebraMap L F r).prod ∈ S := by
      apply Subring.multiset_prod_mem
      intro y hy
      obtain ⟨r', hr', rfl⟩ := Multiset.mem_map.mp hy
      obtain ⟨c', -, hc'⟩ := hm' r' hr'
      rw [← hc']
      exact S.sub_mem hT (hAS c')
    apply ih hm'
    apply hcancel _ (O.mul_mem hfO (hSO hprodS))
    rw [Multiset.map_cons, Multiset.prod_cons] at hfm
    rw [hcr]
    have : f * (m.map fun r => T - algebraMap L F r).prod * (T - algebraMap L F r) =
      f * ((T - algebraMap L F r) * (m.map fun r => T - algebraMap L F r).prod) := by ring
    rwa [this]


-- created on 2026-10-20
