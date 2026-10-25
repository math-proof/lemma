/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean -/

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Def.NumberTheory.SelbergSieve
import Lemma.Nat.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocals.Part4
/-!
# Brun's theorem on twin-prime reciprocals

This file records the convergence of the reciprocal series over twin-prime pairs.
-/


section

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

open MathlibExt.SelbergSieve

-- N6(b): nu agrees with brunF on divisors of P
theorem brunSieve_nu_eq_brunF (Y N l : ℕ)
    (hl : l ∣ brunP Y) : (brunSieve Y N).nu l = brunF l := by
  have hdvd : l ∣ (brunSieve Y N).prodPrimes := hl
  have hprod := BoundingSieve.prod_primeFactors_nu
    (s := brunSieve Y N) (d := l) hdvd
  have hsq : Squarefree l :=
    BoundingSieve.squarefree_of_dvd_prodPrimes
      (s := brunSieve Y N) hdvd
  have hback : ∏ p ∈ l.primeFactors, p = l :=
    Nat.prod_primeFactors_of_squarefree hsq
  have hterm : ∀ p ∈ l.primeFactors,
      (brunSieve Y N).nu p = brunF p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpl : p ∣ l := Nat.dvd_of_mem_primeFactors hp
    have hpP : p ∣ brunP Y := dvd_trans hpl hl
    have hchar := (brunP_prime_dvd Y p hpp).mp hpP
    obtain ⟨hp2, -⟩ := hchar
    have hnu : (brunSieve Y N).nu p = 2 / (p : ℝ) := by
      change brunNu p = _
      exact brunNu_odd_prime p hpp hp2
    rw [hnu, brunF_odd_prime p hpp hp2]
  have hmap : brunF (∏ p ∈ l.primeFactors, p) =
      ∏ p ∈ l.primeFactors, brunF p := map_prod brunF _ _
  have hnu_eq : (brunSieve Y N).nu l =
      ∏ p ∈ l.primeFactors, brunF p := by
    rw [← hprod]
    exact Finset.prod_congr rfl hterm
  rw [hback] at hmap
  rw [hnu_eq, ← hmap]

-- N6(c): fiber sum bound via Euler product
theorem brunSieve_fiber_le (Y N l : ℕ) (hl : l ∣ brunP Y)
    (T : Finset ℕ)
    (hT : ∀ m ∈ T, m ∈ Nat.factoredNumbers l.primeFactors) :
    ∑ m ∈ T, brunF (l * m) ≤ (brunSieve Y N).selbergTerms l := by
  have hdvd : l ∣ (brunSieve Y N).prodPrimes := hl
  have hsel : (brunSieve Y N).selbergTerms l =
      brunF l * ∏ p ∈ l.primeFactors, (1 - brunF p)⁻¹ := by
    rw [BoundingSieve.selbergTerms_apply]
    have hnu_l : (brunSieve Y N).nu l = brunF l :=
      brunSieve_nu_eq_brunF Y N l hl
    have hnu_p : ∀ p ∈ l.primeFactors,
        (brunSieve Y N).nu p = brunF p := by
      intro p hp
      have hpl : p ∣ l := Nat.dvd_of_mem_primeFactors hp
      exact brunSieve_nu_eq_brunF Y N p (dvd_trans hpl hl)
    rw [hnu_l]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [hnu_p p hp]
  have heuler := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := brunF) (fun {p} hp => brunF_norm_prime p hp) l.primeFactors
  obtain ⟨-, hhas⟩ := heuler
  have hfilter : l.primeFactors.filter (fun p => p.Prime) =
      l.primeFactors := by
    apply Finset.filter_true_of_mem
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  rw [hfilter] at hhas
  have hsub_le : ∑ m ∈ Finset.subtype
        (fun m => m ∈ Nat.factoredNumbers l.primeFactors) T,
        brunF (↑m : ℕ) ≤ ∏ p ∈ l.primeFactors, (1 - brunF p)⁻¹ := by
    exact sum_le_hasSum _ (fun i _ => brunF_nonneg ↑i) hhas
  have hsub_eq : ∑ m ∈ Finset.subtype
        (fun m => m ∈ Nat.factoredNumbers l.primeFactors) T,
        brunF (↑m : ℕ) = ∑ m ∈ T, brunF m :=
    Finset.sum_subtype_of_mem brunF hT
  have hF_nonneg : 0 ≤ brunF l := brunF_nonneg l
  calc ∑ m ∈ T, brunF (l * m)
      = ∑ m ∈ T, brunF l * brunF m := by
        apply Finset.sum_congr rfl
        intro m _
        exact map_mul brunF l m
    _ = brunF l * ∑ m ∈ T, brunF m := by rw [Finset.mul_sum]
    _ ≤ brunF l * ∏ p ∈ l.primeFactors, (1 - brunF p)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hF_nonneg
        rw [← hsub_eq]
        exact hsub_le
    _ = (brunSieve Y N).selbergTerms l := hsel.symm

theorem sieveLevelSum_brunSieve_ge (Y N : ℕ) (_ : 1 ≤ Y) :
    (∑ n ∈ (Finset.Icc 1 (Y ^ 2)).filter Odd, brunF n) ≤
      levelSum (brunSieve Y N) (Y ^ 2) := by
  set B : Finset ℕ := (Finset.Icc 1 (Y ^ 2)).filter Odd with hB
  set L : Finset ℕ := levelSet (brunSieve Y N) (Y ^ 2) with hL
  have hP0 : brunP Y ≠ 0 := brunP_ne_zero Y
  have hP0' : (brunSieve Y N).prodPrimes ≠ 0 := hP0
  have hmaps : ∀ n ∈ B, (∏ p ∈ n.primeFactors, p) ∈ L := by
    intro n hn
    simp only [hB, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h1n, h2n⟩, hoddn⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hrdvd : (∏ p ∈ n.primeFactors, p) ∣ n :=
      Nat.prod_primeFactors_dvd n
    have hrle : (∏ p ∈ n.primeFactors, p) ≤ Y ^ 2 :=
      le_trans (Nat.le_of_dvd hnpos hrdvd) h2n
    have hsub : n.primeFactors ⊆ brunPrimes Y := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hp2 : p ≠ 2 := by
        intro h2
        subst h2
        exact (by decide : ¬ Odd 2) (hoddn.of_dvd_nat hpdvd)
      have hple : p ≤ Y ^ 2 :=
        le_trans (Nat.le_of_dvd hnpos hpdvd) h2n
      simp only [brunPrimes, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_iff.mpr hple, hpp, hp2⟩
    have hrP : (∏ p ∈ n.primeFactors, p) ∣ brunP Y := by
      unfold brunP
      exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
    simp only [hL, levelSet, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hrP, hP0'⟩, hrle⟩
  have hfib : (∑ n ∈ B, brunF n) =
      ∑ l ∈ L, ∑ n ∈ B.filter
        (fun n => (∏ p ∈ n.primeFactors, p) = l), brunF n := by
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
  rw [hfib]
  unfold levelSum
  rw [← hL]
  apply Finset.sum_le_sum
  intro l hl
  simp only [hL, levelSet, Finset.mem_filter,
    Nat.mem_divisors] at hl
  obtain ⟨⟨hlP, -⟩, -⟩ := hl
  have hlY : l ∣ brunP Y := hlP
  have hl0 : l ≠ 0 := by
    intro h0
    subst h0
    simp only [zero_dvd_iff] at hlP
    exact hP0 hlP
  -- Fiber and image
  set F : Finset ℕ :=
    B.filter (fun n => (∏ p ∈ n.primeFactors, p) = l) with hF
  set T : Finset ℕ := F.image (fun n => n / l) with hT
  have hmem_T : ∀ m ∈ T, m ∈ Nat.factoredNumbers l.primeFactors := by
    intro m hm
    simp only [hT, Finset.mem_image] at hm
    obtain ⟨n, hnF, rfl⟩ := hm
    simp only [hF, hB, Finset.mem_filter, Finset.mem_Icc] at hnF
    obtain ⟨⟨⟨h1n, -⟩, -⟩, hrn⟩ := hnF
    have hn0 : n ≠ 0 := by omega
    have hln : l ∣ n := hrn ▸ Nat.prod_primeFactors_dvd n
    have hprime_eq : n.primeFactors = l.primeFactors := by
      have h1 : (∏ p ∈ n.primeFactors, p).primeFactors =
          n.primeFactors := Nat.primeFactors_prod
        (fun p hp => Nat.prime_of_mem_primeFactors hp)
      rw [hrn] at h1
      exact h1.symm
    have hn_fact : n ∈ Nat.factoredNumbers l.primeFactors := by
      apply Nat.mem_factoredNumbers_of_primeFactors_subset hn0
      rw [← hprime_eq]
    have hdiv : n / l ∣ n := by
      have hmul := Nat.mul_div_cancel' hln
      exact ⟨l, by rw [mul_comm]; exact hmul.symm⟩
    exact Nat.mem_factoredNumbers_of_dvd hn_fact hdiv
  have hsum_eq : (∑ n ∈ F, brunF n) =
      ∑ m ∈ T, brunF (l * m) := by
    have hinj : Set.InjOn (fun n => n / l) (↑F : Set ℕ) := by
      intro n1 hn1 n2 hn2 heq
      simp only [hF, Finset.mem_coe, Finset.mem_filter] at hn1 hn2
      obtain ⟨-, hrn1⟩ := hn1
      obtain ⟨-, hrn2⟩ := hn2
      have hln1 : l ∣ n1 := hrn1 ▸ Nat.prod_primeFactors_dvd n1
      have hln2 : l ∣ n2 := hrn2 ▸ Nat.prod_primeFactors_dvd n2
      have e1 : l * (n1 / l) = n1 := Nat.mul_div_cancel' hln1
      have e2 : l * (n2 / l) = n2 := Nat.mul_div_cancel' hln2
      have heq' : n1 / l = n2 / l := heq
      rw [← e1, ← e2, heq']
    have himg := Finset.sum_image (s := F) (g := fun n => n / l)
      (f := fun m => brunF (l * m)) hinj
    rw [← hT] at himg
    rw [himg]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [hF, Finset.mem_filter] at hn
    obtain ⟨-, hrn⟩ := hn
    have hln : l ∣ n := hrn ▸ Nat.prod_primeFactors_dvd n
    have e : l * (n / l) = n := Nat.mul_div_cancel' hln
    rw [e]
  rw [hsum_eq]
  exact brunSieve_fiber_le Y N l hlY T hmem_T

theorem brunTwinCount_le (Y N : ℕ) (hY : 1 ≤ Y) :
    (brunTwinCount N : ℝ) ≤ (Y : ℝ) ^ 2 + 1 +
      4 * (N : ℝ) / (Real.log ((Y : ℝ) + 1)) ^ 2 + (Y : ℝ) ^ 24 := by
  have hP0 : brunP Y ≠ 0 := brunP_ne_zero Y
  -- (i) Split twins
  set T : Finset ℕ :=
    (Finset.range N).filter (fun p => p.Prime ∧ (p + 2).Prime) with hT
  have hTcard : T.card = brunTwinCount N := rfl
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := T) (fun p => p ≤ Y ^ 2)
  -- Small twins ≤ Y^2+1
  have hsmall_le : ((T.filter (fun p => p ≤ Y ^ 2)).card : ℝ) ≤
      (Y : ℝ) ^ 2 + 1 := by
    have hsub : T.filter (fun p => p ≤ Y ^ 2) ⊆
        Finset.range (Y ^ 2 + 1) := by
      intro p hp
      simp only [hT, Finset.mem_filter, Finset.mem_range] at hp ⊢
      obtain ⟨⟨-, -⟩, hle⟩ := hp
      exact Nat.lt_succ_iff.mpr hle
    calc ((T.filter (fun p => p ≤ Y ^ 2)).card : ℝ)
        ≤ ((Finset.range (Y ^ 2 + 1)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = (Y : ℝ) ^ 2 + 1 := by
          rw [Finset.card_range]
          push_cast
          ring
  -- Large twins are sifted
  have hlarge_sub : T.filter (fun p => ¬ p ≤ Y ^ 2) ⊆
      (Finset.range N).filter
        (fun n => Nat.Coprime (brunP Y) (n * (n + 2))) := by
    intro p hp
    simp only [hT, Finset.mem_filter, Finset.mem_range] at hp ⊢
    obtain ⟨⟨hmem, hpp, hp2⟩, hle⟩ := hp
    have hge : Y ^ 2 + 1 ≤ p := by omega
    refine ⟨hmem, ?_⟩
    apply Nat.coprime_of_dvd
    intro q hq hqP hqdiv
    have hchar := (brunP_prime_dvd Y q hq).mp hqP
    obtain ⟨hq2, hqle⟩ := hchar
    rcases (hq.dvd_mul.mp hqdiv) with h | h
    · have heq : q = p :=
        (Nat.prime_dvd_prime_iff_eq hq hpp).mp h
      omega
    · have heq : q = p + 2 :=
        (Nat.prime_dvd_prime_iff_eq hq hp2).mp h
      omega
  have hlarge_le : ((T.filter (fun p => ¬ p ≤ Y ^ 2)).card : ℝ) ≤
      (brunSieve Y N).siftedSum := by
    rw [brunSieve_siftedSum]
    exact_mod_cast Finset.card_le_card hlarge_sub
  have hcount : (brunTwinCount N : ℝ) ≤ (Y : ℝ) ^ 2 + 1 +
      (brunSieve Y N).siftedSum := by
    have h1 : (T.card : ℝ) = ((T.filter (fun p => p ≤ Y ^ 2)).card : ℝ) +
        ((T.filter (fun p => ¬ p ≤ Y ^ 2)).card : ℝ) := by
      have h := hsplit
      -- hsplit : (filter p).card + (filter ¬p).card = T.card. Need cast.
      have hcast : (((T.filter (fun p => p ≤ Y ^ 2)).card +
          (T.filter (fun p => ¬ p ≤ Y ^ 2)).card : ℕ) : ℝ) =
          (T.card : ℝ) := by exact_mod_cast h
      push_cast at hcast
      linarith [hcast]
    rw [hTcard] at h1
    linarith [h1, hsmall_le, hlarge_le]
  -- (ii) Selberg bound
  have hR1 : 1 ≤ Y ^ 2 := by
    have h := Nat.pow_le_pow_left hY 2
    simpa using h
  have hupper := BoundingSieve.upperMoebius_lambdaSquared
    (levelWeights (brunSieve Y N) (Y ^ 2))
    (levelWeights_one (brunSieve Y N) (Y ^ 2) hR1)
  have hsieve := BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
    (s := brunSieve Y N)
    (BoundingSieve.lambdaSquared (levelWeights (brunSieve Y N) (Y ^ 2)))
    hupper
  have hmain := levelWeights_mainSum (brunSieve Y N) (Y ^ 2) hR1
  have hν : ∀ d : ℕ, d ∣ (brunSieve Y N).prodPrimes →
      1 ≤ (d : ℝ) * (brunSieve Y N).nu d := by
    intro d hdvd
    have hdvd' : d ∣ brunP Y := hdvd
    have hd0 : d ≠ 0 := by
      intro h0
      subst h0
      simp only [zero_dvd_iff] at hdvd'
      exact hP0 hdvd'
    have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd0
    have hrho := brunRho_pos d hd1
    have hnu : (brunSieve Y N).nu d =
        (brunRho d : ℝ) / (d : ℝ) := by
      change brunNu d = _
      rw [brunNu_apply]
    rw [hnu]
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
    have heq : (d : ℝ) * ((brunRho d : ℝ) / (d : ℝ)) =
        (brunRho d : ℝ) := by field_simp
    rw [heq]
    exact_mod_cast hrho
  have hrem' : ∀ d : ℕ, d ∣ (brunSieve Y N).prodPrimes →
      |(brunSieve Y N).rem d| ≤ (d : ℝ) := by
    intro d hdvd
    have hdvd' : d ∣ brunP Y := hdvd
    have hd0 : d ≠ 0 := by
      intro h0
      subst h0
      simp only [zero_dvd_iff] at hdvd'
      exact hP0 hdvd'
    exact brunSieve_abs_rem_le Y N d (Nat.pos_of_ne_zero hd0)
  have herr := levelWeights_errSum_le (brunSieve Y N) (Y ^ 2)
    hR1 hν hrem'
  -- totalMass = N
  have htotal : (brunSieve Y N).totalMass = (N : ℝ) := rfl
  rw [htotal, hmain] at hsieve
  -- errSum ≤ Y^24
  have herr24 : (brunSieve Y N).errSum
      (BoundingSieve.lambdaSquared
        (levelWeights (brunSieve Y N) (Y ^ 2))) ≤
      (Y : ℝ) ^ 24 := by
    calc (brunSieve Y N).errSum _ ≤ ((Y ^ 2 : ℕ) : ℝ) ^ 12 := herr
      _ = (Y : ℝ) ^ 24 := by
          push_cast
          ring
  -- (iii) G lower bound
  have hlog_pos : 0 < Real.log ((Y : ℝ) + 1) := by
    apply Real.log_pos
    have hYpos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
    linarith
  have hlog_nonneg : 0 ≤ Real.log ((Y : ℝ) + 1) := le_of_lt hlog_pos
  have h9 := log_add_one_le_two_mul_oddHarmonic Y
  have h8 := sq_oddHarmonic_le_sum_brunF Y
  have h7 := sieveLevelSum_brunSieve_ge Y N hY
  have hGpos : 0 < levelSum (brunSieve Y N) (Y ^ 2) := by
    have h1 := levelSum_ge_one (brunSieve Y N) (Y ^ 2) hR1
    linarith
  have hsq_le : (Real.log ((Y : ℝ) + 1)) ^ 2 ≤
      4 * levelSum (brunSieve Y N) (Y ^ 2) := by
    have hpow : (Real.log ((Y : ℝ) + 1)) ^ 2 ≤
        (2 * oddHarmonic Y) ^ 2 :=
      pow_le_pow_left₀ hlog_nonneg h9 2
    have hexpand : (2 * oddHarmonic Y) ^ 2 =
        4 * (oddHarmonic Y) ^ 2 := by ring
    rw [hexpand] at hpow
    have hsum_le : (oddHarmonic Y) ^ 2 ≤
        levelSum (brunSieve Y N) (Y ^ 2) :=
      le_trans h8 h7
    have h4 : 4 * (oddHarmonic Y) ^ 2 ≤
        4 * levelSum (brunSieve Y N) (Y ^ 2) := by
      apply mul_le_mul_of_nonneg_left hsum_le (by norm_num)
    linarith [hpow, h4]
  -- (iv) N/G ≤ 4N/log^2
  have hNdiv : (N : ℝ) * (1 / levelSum (brunSieve Y N) (Y ^ 2)) ≤
      4 * (N : ℝ) / (Real.log ((Y : ℝ) + 1)) ^ 2 := by
    have hlog2pos : 0 < (Real.log ((Y : ℝ) + 1)) ^ 2 := by positivity
    have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    rw [mul_one_div, div_le_div_iff₀ hGpos hlog2pos]
    have h1 : (N : ℝ) * (Real.log ((Y : ℝ) + 1)) ^ 2 ≤
        (N : ℝ) * (4 * levelSum (brunSieve Y N) (Y ^ 2)) :=
      mul_le_mul_of_nonneg_left hsq_le hNnonneg
    have h2 : (N : ℝ) * (4 * levelSum (brunSieve Y N) (Y ^ 2)) =
        4 * (N : ℝ) * levelSum (brunSieve Y N) (Y ^ 2) := by ring
    rw [h2] at h1
    exact h1
  linarith [hcount, hsieve, herr24, hNdiv]

/-- The sum of reciprocals over twin-prime pairs, indexed by the smaller prime
`p` of each pair `(p, p + 2)`, converges over `ℝ`; a shared prime such as `5`
is intentionally counted once in each of `(3, 5)` and `(5, 7)`, and a finite
collection of twin-prime pairs is already covered because a finitely supported
function is summable.

Source: Alexei Kourbatov and Marek Wolf, "On the First Occurrences of Gaps
Between Primes in a Residue Class," Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Wolf/wolf2.tex`, lines 684–705;
live and bundled source SHA-256
`f19705a8cece7b19aea01b0669774f24e42d49f9a262ff1c6ea0b4e6644e6d64` and exact
cited span SHA-256
`dd71eb411be0ec74f9b3599bfdc17309c68109e03167163b629ab5949415e8da`.
Corroboration: Prapanpong Pongsriiam and Kota Saito, "Palindromes and
Antipalindromes in Short Intervals," Journal of Integer Sequences 26 (2023),
`https://cs.uwaterloo.ca/journals/JIS/VOL26/Saito/saito1.tex`, lines 205–210;
live and bundled source SHA-256
`0c721e5603affcd1b7a1dfeb67dcc79ef6a28132308cb081a1ee39c12515fabc` and exact
cited span SHA-256
`b28ebf74254fb808313c73f910a0f7978dbae8e6987027c94e6924a6d81cc47f`.
The sources attribute the theorem to V. Brun's 1919 paper on convergence or
finiteness of the reciprocal twin-prime series.

Proves `Wanted` entry `brun_twin_prime_reciprocal_series_summable`.
-/
theorem brun_twin_prime_reciprocal_series_summable :
    Summable (fun p : ℕ =>
      if p.Prime ∧ (p + 2).Prime then
        (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ)
      else 0) := by
  set B : ℕ := (2 ^ 32 : ℕ) with hBdef
  have hB2 : 2 ≤ B := by
    rw [hBdef]
    norm_num
  have hBpos : 0 < B := by omega
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set L : ℝ := (2 ^ 37 : ℝ) / (Real.log 2) ^ 2 with hLdef
  set c : ℕ → ℝ := fun j => 6 * ((1 / 2 : ℝ) ^ j) + L * (1 / ((((j + 1 : ℕ)) : ℝ) ^ 2))
    with hcdef
  have hgeo : Summable (fun j : ℕ => ((1 / 2 : ℝ)) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hgeo6 : Summable (fun j : ℕ => 6 * ((1 / 2 : ℝ) ^ j)) := hgeo.mul_left 6
  have hp : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun j : ℕ => 1 / (((((j + 1 : ℕ)) : ℝ) ^ 2))) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ) ^ 2)) 1).mpr hp
  have hLsum : Summable (fun j : ℕ => L * (1 / (((((j + 1 : ℕ)) : ℝ) ^ 2)))) :=
    hshift.mul_left L
  have hadd :
      Summable
        (fun j : ℕ => 6 * ((1 / 2 : ℝ) ^ j) + L * (1 / (((((j + 1 : ℕ)) : ℝ) ^ 2)))) :=
    hgeo6.add hLsum
  have hc : Summable c := by
    rw [hcdef]
    exact hadd
  refine summable_of_sum_Ico_pow_le _ c B hB2 ?_ hc ?_
  · intro n
    by_cases h : n.Prime ∧ (n + 2).Prime
    · simp only [h]
      positivity
    · simp only [h, ↓reduceIte, le_refl]
  · intro j
    set Bj : ℕ := B ^ j with hBjdef
    set Bj1 : ℕ := B ^ (j + 1) with hBj1def
    set Y : ℕ := 2 ^ j with hYdef
    have hBjpos : 0 < Bj := Nat.pow_pos hBpos
    have hYpos : 0 < Y := Nat.pow_pos (by norm_num)
    have hY1 : 1 ≤ Y := by omega
    have hBjRpos : (0 : ℝ) < ((Bj : ℕ) : ℝ) := Nat.cast_pos.mpr hBjpos
    have hBjRne : ((Bj : ℕ) : ℝ) ≠ 0 := ne_of_gt hBjRpos
    set Cb : ℝ := 2 / ((Bj : ℕ) : ℝ) with hCbdef
    have hCbnonneg : 0 ≤ Cb := by
      rw [hCbdef]
      positivity
    have hterm : ∀ p ∈ Finset.Ico Bj Bj1,
        (if p.Prime ∧ (p + 2).Prime then
          (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ)
        else 0)
        ≤ (if p.Prime ∧ (p + 2).Prime then Cb else 0) := by
      intro p hp
      by_cases hP : p.Prime ∧ (p + 2).Prime
      · rw [ite_eq_left hP, ite_eq_left hP]
        have hmem := Finset.mem_Ico.mp hp
        have hplo : Bj ≤ p := hmem.1
        have hBj_le_p : ((Bj : ℕ) : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hplo
        have hBj_le_p2 : ((Bj : ℕ) : ℝ) ≤ ((((p + 2 : ℕ))) : ℝ) := by
          have hle : Bj ≤ p + 2 := le_trans hplo (Nat.le_add_right p 2)
          exact Nat.cast_le.mpr hle
        have h1 : (1 : ℝ) / (p : ℝ) ≤ 1 / ((Bj : ℕ) : ℝ) :=
          one_div_le_one_div_of_le hBjRpos hBj_le_p
        have h2 : (1 : ℝ) / ((((p + 2 : ℕ))) : ℝ) ≤ 1 / ((Bj : ℕ) : ℝ) :=
          one_div_le_one_div_of_le hBjRpos hBj_le_p2
        have hsum : (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((((p + 2 : ℕ))) : ℝ) ≤
            1 / ((Bj : ℕ) : ℝ) + 1 / ((Bj : ℕ) : ℝ) := add_le_add h1 h2
        have hCb_eq : (1 : ℝ) / ((Bj : ℕ) : ℝ) + 1 / ((Bj : ℕ) : ℝ) = Cb := by
          rw [hCbdef]
          field_simp
          ring
        linarith [hsum, hCb_eq]
      · rw [ite_eq_right hP, ite_eq_right hP]
    have hsum_le : ∑ p ∈ Finset.Ico Bj Bj1,
          (if p.Prime ∧ (p + 2).Prime then
            (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ)
          else 0)
        ≤ ∑ p ∈ Finset.Ico Bj Bj1, (if p.Prime ∧ (p + 2).Prime then Cb else 0) :=
      Finset.sum_le_sum hterm
    have hRHS : ∑ p ∈ Finset.Ico Bj Bj1, (if p.Prime ∧ (p + 2).Prime then Cb else 0)
        = Cb * (((((Finset.Ico Bj Bj1).filter
          (fun p => p.Prime ∧ (p + 2).Prime)).card : ℕ)) : ℝ) := by
      have hterm_eq : ∀ p : ℕ, (if p.Prime ∧ (p + 2).Prime then Cb else 0)
          = Cb * (if p.Prime ∧ (p + 2).Prime then (1 : ℝ) else 0) := by
        intro p
        by_cases hP : p.Prime ∧ (p + 2).Prime
        · rw [ite_eq_left hP, ite_eq_left hP, mul_one]
        · rw [ite_eq_right hP, ite_eq_right hP, mul_zero]
      simp_rw [hterm_eq, ← Finset.mul_sum]
      rw [Finset.sum_boole]
    have hIco_sub : Finset.Ico Bj Bj1 ⊆ Finset.range Bj1 := by
      intro x hx
      simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
      exact hx.2
    have hfilter_sub : (Finset.Ico Bj Bj1).filter (fun p => p.Prime ∧ (p + 2).Prime)
        ⊆ (Finset.range Bj1).filter (fun p => p.Prime ∧ (p + 2).Prime) := by
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hIco_sub hx.1, hx.2⟩
    have hcard_le : (((((Finset.Ico Bj Bj1).filter
        (fun p => p.Prime ∧ (p + 2).Prime)).card : ℕ)) : ℝ) ≤ (brunTwinCount Bj1 : ℝ) := by
      have hle : ((Finset.Ico Bj Bj1).filter (fun p => p.Prime ∧ (p + 2).Prime)).card ≤
          brunTwinCount Bj1 := by
        unfold brunTwinCount
        exact Finset.card_le_card hfilter_sub
      exact_mod_cast hle
    have hblock_le : ∑ p ∈ Finset.Ico Bj Bj1,
          (if p.Prime ∧ (p + 2).Prime then
            (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ)
          else 0)
        ≤ Cb * (brunTwinCount Bj1 : ℝ) := by
      have hle1 : ∑ p ∈ Finset.Ico Bj Bj1,
            (if p.Prime ∧ (p + 2).Prime then
              (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ)
            else 0)
          ≤ Cb * (((((Finset.Ico Bj Bj1).filter
            (fun p => p.Prime ∧ (p + 2).Prime)).card : ℕ)) : ℝ) := by
        calc ∑ p ∈ Finset.Ico Bj Bj1,
              (if p.Prime ∧ (p + 2).Prime then
                (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ)
              else 0)
            ≤ ∑ p ∈ Finset.Ico Bj Bj1, (if p.Prime ∧ (p + 2).Prime then Cb else 0) :=
              hsum_le
          _ = Cb * (((((Finset.Ico Bj Bj1).filter
              (fun p => p.Prime ∧ (p + 2).Prime)).card : ℕ)) : ℝ) := hRHS
      have hle2 : Cb * (((((Finset.Ico Bj Bj1).filter
          (fun p => p.Prime ∧ (p + 2).Prime)).card : ℕ)) : ℝ)
          ≤ Cb * (brunTwinCount Bj1 : ℝ) :=
        mul_le_mul_of_nonneg_left hcard_le hCbnonneg
      exact le_trans hle1 hle2
    have hN13 := brunTwinCount_le Y Bj1 hY1
    have hCb_mul : Cb * (brunTwinCount Bj1 : ℝ)
        ≤ Cb * (((Y : ℝ) ^ 2 + 1 + 4 * ((Bj1 : ℕ) : ℝ) / (Real.log ((Y : ℝ) + 1)) ^ 2 +
          (Y : ℝ) ^ 24)) :=
      mul_le_mul_of_nonneg_left hN13 hCbnonneg
    have hleCb : ∑ p ∈ Finset.Ico Bj Bj1,
          (if p.Prime ∧ (p + 2).Prime then
            (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ)
          else 0)
        ≤ Cb * (((Y : ℝ) ^ 2 + 1 + 4 * ((Bj1 : ℕ) : ℝ) / (Real.log ((Y : ℝ) + 1)) ^ 2 +
          (Y : ℝ) ^ 24)) :=
      le_trans hblock_le hCb_mul
    have hYsq : ((Y : ℕ) : ℝ) ^ 2 = (2 : ℝ) ^ (2 * j) := by
      rw [hYdef]
      exact brun_cast_Y_sq j
    have hY24 : ((Y : ℕ) : ℝ) ^ 24 = (2 : ℝ) ^ (24 * j) := by
      rw [hYdef]
      exact brun_cast_Y_pow24 j
    have hBjcast : ((Bj : ℕ) : ℝ) = (2 : ℝ) ^ (32 * j) := by
      rw [hBjdef, hBdef]
      exact brun_cast_Bj j
    have hXpos : (0 : ℝ) < (2 : ℝ) ^ (32 * j) := by positivity
    have hXne : (2 : ℝ) ^ (32 * j) ≠ 0 := ne_of_gt hXpos
    have hpow1 := brun_pow2_add_one_div_le j
    have hterm1 : Cb * (((Y : ℕ) : ℝ) ^ 2 + 1) ≤ 4 * ((1 / 2 : ℝ) ^ j) := by
      rw [hCbdef, hYsq, hBjcast]
      have heq : (2 / (2 : ℝ) ^ (32 * j)) * ((2 : ℝ) ^ (2 * j) + 1)
          = 2 * (((2 : ℝ) ^ (2 * j) + 1) / (2 : ℝ) ^ (32 * j)) := by
        field_simp
      rw [heq]
      have hmul : 2 * (((2 : ℝ) ^ (2 * j) + 1) / (2 : ℝ) ^ (32 * j))
          ≤ 2 * (2 * ((1 / 2 : ℝ) ^ j)) :=
        mul_le_mul_of_nonneg_left hpow1 (by norm_num)
      have h4 : (2 : ℝ) * (2 * ((1 / 2 : ℝ) ^ j)) = 4 * ((1 / 2 : ℝ) ^ j) := by ring
      rw [h4] at hmul
      exact hmul
    have hpow3 := brun_pow24_div_le j
    have hterm3 : Cb * (((Y : ℕ) : ℝ) ^ 24) ≤ 2 * ((1 / 2 : ℝ) ^ j) := by
      rw [hCbdef, hY24, hBjcast]
      have heq : (2 / (2 : ℝ) ^ (32 * j)) * ((2 : ℝ) ^ (24 * j))
          = 2 * (((2 : ℝ) ^ (24 * j)) / (2 : ℝ) ^ (32 * j)) := by
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_left hpow3 (by norm_num)
    have hBj1_eq : Bj1 = Bj * B := by
      rw [hBj1def, hBjdef]
      exact pow_succ B j
    have hBj1R : ((Bj1 : ℕ) : ℝ) = ((Bj : ℕ) : ℝ) * ((B : ℕ) : ℝ) := by
      rw [hBj1_eq, Nat.cast_mul]
    have hBR : ((B : ℕ) : ℝ) = (2 : ℝ) ^ 32 := by
      rw [hBdef]
      push_cast
      ring
    have h8B : 8 * ((B : ℕ) : ℝ) = (2 : ℝ) ^ 35 := by
      rw [hBR]
      have h8 : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      rw [h8, ← pow_add]
    have hYposR : (0 : ℝ) < ((Y : ℕ) : ℝ) := Nat.cast_pos.mpr hYpos
    have hlogYpos : 0 < Real.log (((Y : ℕ) : ℝ) + 1) :=
      Real.log_pos (by linarith)
    have hlogY2pos : (0 : ℝ) < (Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2 := by positivity
    have hlogY2ne : (Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2 ≠ 0 := ne_of_gt hlogY2pos
    have hj1pos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ)) := by
      have h : (0 : ℕ) < j + 1 := Nat.succ_pos j
      exact_mod_cast h
    have hj1sqpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := pow_pos hj1pos 2
    have hj1sqne : ((((j + 1 : ℕ)) : ℝ) ^ 2) ≠ 0 := ne_of_gt hj1sqpos
    have hlog2sqpos : (0 : ℝ) < (Real.log 2) ^ 2 := pow_pos hlog2pos 2
    have hlog2sqne : (Real.log 2) ^ 2 ≠ 0 := ne_of_gt hlog2sqpos
    have hlogineq0 := brun_log_mul_le j
    have hYcast_eq : ((((2 ^ j : ℕ)) : ℝ)) = ((Y : ℕ) : ℝ) := by rw [hYdef]
    have hlogineq : ((((j + 1 : ℕ)) : ℝ)) * Real.log 2
        ≤ 2 * Real.log (((Y : ℕ) : ℝ) + 1) := by
      have h := hlogineq0
      rw [hYcast_eq] at h
      exact h
    have ha_nonneg : (0 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ)) * Real.log 2 :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt hlog2pos)
    have hsq : ((((j + 1 : ℕ)) : ℝ) * Real.log 2) ^ 2
        ≤ (2 * Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2 :=
      pow_le_pow_left₀ ha_nonneg hlogineq 2
    have hsq' : ((((j + 1 : ℕ)) : ℝ) ^ 2) * ((Real.log 2) ^ 2)
        ≤ 4 * ((Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2) := by
      have hL : ((((j + 1 : ℕ)) : ℝ) * Real.log 2) ^ 2
          = ((((j + 1 : ℕ)) : ℝ) ^ 2) * ((Real.log 2) ^ 2) := by ring
      have hR : (2 * Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2
          = 4 * ((Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2) := by ring
      rw [hL, hR] at hsq
      exact hsq
    have h2_35pos : (0 : ℝ) < (2 : ℝ) ^ 35 := by positivity
    have h237 : (2 : ℝ) ^ 37 = 4 * (2 : ℝ) ^ 35 := by
      have h : (37 : ℕ) = 35 + 2 := by norm_num
      rw [h, pow_add]
      norm_num
    have hterm2 : Cb * (4 * ((Bj1 : ℕ) : ℝ) / (Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2)
        ≤ L * (1 / (((((j + 1 : ℕ)) : ℝ) ^ 2))) := by
      rw [hCbdef, hBj1R]
      have hLHS_eq : (2 / ((Bj : ℕ) : ℝ)) *
            (4 * (((Bj : ℕ) : ℝ) * ((B : ℕ) : ℝ)) / (Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2)
          = (8 * ((B : ℕ) : ℝ)) / (Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2 := by
        field_simp
        ring
      rw [hLHS_eq, h8B, hLdef]
      have hDpos : (0 : ℝ) < (Real.log 2) ^ 2 * ((((j + 1 : ℕ)) : ℝ) ^ 2) :=
        mul_pos hlog2sqpos hj1sqpos
      have hRHS_eq : ((2 : ℝ) ^ 37 / (Real.log 2) ^ 2) * (1 / (((((j + 1 : ℕ)) : ℝ) ^ 2)))
          = (2 : ℝ) ^ 37 / ((Real.log 2) ^ 2 * (((((j + 1 : ℕ)) : ℝ) ^ 2))) := by
        field_simp
      rw [hRHS_eq, div_le_div_iff₀ hlogY2pos hDpos]
      have hmul := mul_le_mul_of_nonneg_left hsq' (le_of_lt h2_35pos)
      have hLHS_rw : (2 : ℝ) ^ 35 * ((Real.log 2) ^ 2 * (((((j + 1 : ℕ)) : ℝ) ^ 2)))
          = (2 : ℝ) ^ 35 * ((((((j + 1 : ℕ)) : ℝ) ^ 2) * ((Real.log 2) ^ 2))) := by
        ring
      have hRHS_rw : (2 : ℝ) ^ 37 * ((Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2)
          = (2 : ℝ) ^ 35 * (4 * ((Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2)) := by
        rw [h237]
        ring
      rw [hLHS_rw, hRHS_rw]
      exact hmul
    have hexpand : Cb * (((Y : ℝ) ^ 2 + 1 + 4 * ((Bj1 : ℕ) : ℝ) /
        (Real.log ((Y : ℝ) + 1)) ^ 2 + (Y : ℝ) ^ 24))
        = Cb * (((Y : ℕ) : ℝ) ^ 2 + 1) +
          Cb * (4 * ((Bj1 : ℕ) : ℝ) / (Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2) +
          Cb * (((Y : ℕ) : ℝ) ^ 24) := by
      ring
    have hc_eq : c j = 6 * ((1 / 2 : ℝ) ^ j) + L * (1 / (((((j + 1 : ℕ)) : ℝ) ^ 2))) :=
      rfl
    rw [hexpand] at hleCb
    have hfinal : Cb * (((Y : ℕ) : ℝ) ^ 2 + 1) +
          Cb * (4 * ((Bj1 : ℕ) : ℝ) / (Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2) +
          Cb * (((Y : ℕ) : ℝ) ^ 24)
        ≤ 6 * ((1 / 2 : ℝ) ^ j) + L * (1 / (((((j + 1 : ℕ)) : ℝ) ^ 2))) := by
      have h13 : Cb * (((Y : ℕ) : ℝ) ^ 2 + 1) + Cb * (((Y : ℕ) : ℝ) ^ 24)
          ≤ 4 * ((1 / 2 : ℝ) ^ j) + 2 * ((1 / 2 : ℝ) ^ j) := add_le_add hterm1 hterm3
      have h6 : (4 : ℝ) * ((1 / 2 : ℝ) ^ j) + 2 * ((1 / 2 : ℝ) ^ j)
          = 6 * ((1 / 2 : ℝ) ^ j) := by ring
      linarith [h13, hterm2, h6]
    have hle_c : Cb * (((Y : ℕ) : ℝ) ^ 2 + 1) +
          Cb * (4 * ((Bj1 : ℕ) : ℝ) / (Real.log (((Y : ℕ) : ℝ) + 1)) ^ 2) +
          Cb * (((Y : ℕ) : ℝ) ^ 24)
        ≤ c j := by
      rw [hc_eq]
      exact hfinal
    exact le_trans hleCb hle_c

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted
end
