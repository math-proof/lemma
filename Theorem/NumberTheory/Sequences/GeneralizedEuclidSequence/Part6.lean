/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/GeneralizedEuclidSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.List.GetD
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.GroupTheory.GroupAction.Quotient
import Def.NumberTheory.Sequences.GeneralizedEuclidSequence.Part6
/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/


namespace MetaMathlibExt

open scoped Pointwise

theorem good_nil (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) : Good P P.toList := by
  refine ⟨List.prefix_refl _, Finset.nodup_toList P, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_toList] at hx
    exact hP x hx
  · intro j hj1 hj2
    rw [Finset.length_toList] at hj2
    omega

/-- Appending a prime divisor of `N_I` preserves validity. -/
theorem good_append (P : Finset ℕ) (l : List ℕ) (hg : Good P l) (r : ℕ)
    (hrprime : r.Prime) (hrnotin : r ∉ l) (I : Finset ℕ)
    (hI : I ⊆ Finset.range l.length)
    (hrdvd : r ∣ (∏ i ∈ I, eVal l i) + ∏ i ∈ (Finset.range l.length \ I), eVal l i) :
    Good P (l ++ [r]) := by
  obtain ⟨hpref, hnod, hprime, hwit⟩ := hg
  have hpre : l <+: l ++ [r] := List.prefix_append l [r]
  refine ⟨hpref.trans hpre, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnod, List.nodup_singleton _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact fun h => hrnotin (h ▸ ha)
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hprime x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact hrprime
  · intro j hj1 hj2
    rw [List.length_append, List.length_singleton] at hj2
    by_cases hjn : j < l.length
    · obtain ⟨J, hJ, hdvd⟩ := hwit j hj1 hjn
      have hval : ∀ i ∈ J, eVal l i = eVal (l ++ [r]) i := by
        intro i hi
        have hi' : i < l.length := by
          have h2 := hJ hi
          rw [Finset.mem_range] at h2
          exact lt_of_lt_of_le h2 (Nat.le_of_lt hjn)
        exact eVal_prefix l (l ++ [r]) hpre i hi'
      have hval2 : ∀ i ∈ Finset.range j \ J, eVal l i = eVal (l ++ [r]) i := by
        intro i hi
        rw [Finset.mem_sdiff, Finset.mem_range] at hi
        have hi' : i < l.length := lt_of_lt_of_le hi.1 (Nat.le_of_lt hjn)
        exact eVal_prefix l (l ++ [r]) hpre i hi'
      have hj2' : j < (l ++ [r]).length := by
        rw [List.length_append, List.length_singleton]
        omega
      have hget : (l ++ [r])[j] = l[j] := by
        have e1 := eVal_prefix l (l ++ [r]) hpre j hjn
        rw [eVal_lt l j hjn, eVal_lt (l ++ [r]) j hj2'] at e1
        exact e1.symm
      rw [Finset.prod_congr rfl hval, Finset.prod_congr rfl hval2] at hdvd
      rw [hget]
      exact ⟨J, hJ, hdvd⟩
    · have hjj : j = l.length := by omega
      subst hjj
      have hlen' : l.length < (l ++ [r]).length := by
        rw [List.length_append, List.length_singleton]
        exact Nat.lt_succ_self _
      have hget : (l ++ [r])[l.length] = r := by simp
      have hval : ∀ i ∈ I, eVal (l ++ [r]) i = eVal l i := by
        intro i hi
        have hi' : i < l.length := by
          have h := hI hi
          rwa [Finset.mem_range] at h
        exact (eVal_prefix l (l ++ [r]) hpre i hi').symm
      have hval2 : ∀ i ∈ Finset.range l.length \ I, eVal (l ++ [r]) i = eVal l i := by
        intro i hi
        rw [Finset.mem_sdiff, Finset.mem_range] at hi
        exact (eVal_prefix l (l ++ [r]) hpre i hi.1).symm
      refine ⟨I, hI, ?_⟩
      rw [hget, Finset.prod_congr rfl hval, Finset.prod_congr rfl hval2]
      exact hrdvd

theorem geneuclid_reach_q_of_char_one (P : Finset ℕ) (l : List ℕ)
    (hg : Good P l) (q : ℕ) [Fact q.Prime] [NeZero q]
    (hqnot : q ∉ l) (hfull : geneuclidUnits q l = Finset.univ)
    (hchar : geneuclidQuadChar q (-(geneuclidProduct l : ZMod q)) = 1) :
    ∃ l', l <+: l' ∧ l.length < l'.length ∧ Good P l' ∧ q ∈ l' := by
  have hn0 := geneuclidProduct_ne_zero_mod q l hg.2.2.1 hqnot
  have hminus0 : -(geneuclidProduct l : ZMod q) ≠ 0 := neg_ne_zero.mpr hn0
  have hsquare : IsSquare (-(geneuclidProduct l : ZMod q)) := by
    apply (quadraticChar_one_iff_isSquare hminus0).mp
    change (((quadraticChar (ZMod q)) (-(geneuclidProduct l : ZMod q)) : ℤ) : ℂ) = 1 at hchar
    exact_mod_cast hchar
  obtain ⟨x, hx⟩ := hsquare
  have hx0 : x ≠ 0 := by
    intro h
    apply hminus0
    simpa [h] using hx
  let u := Units.mk0 x hx0
  have hu : u ∈ geneuclidUnits q l := by simp [hfull]
  have hexpr : (u : ZMod q) + (geneuclidProduct l : ZMod q) / (u : ZMod q) = 0 := by
    change x + (geneuclidProduct l : ZMod q) / x = 0
    field_simp
    rw [pow_two, ← hx]
    ring
  have happ : GeneuclidAppendable l q :=
    (geneuclid_q_appendable_iff_expression_zero q l hg.2.2.1 hqnot).mpr ⟨u, hu, hexpr⟩
  obtain ⟨_hq, I, hI, hdvd⟩ := happ
  refine ⟨l ++ [q], List.prefix_append l [q], ?_,
    good_append P l hg q Fact.out hqnot I hI hdvd, by simp⟩
  simp

theorem geneuclid_reach_q_of_full_nonexception (P : Finset ℕ) (l : List ℕ)
    (hg : Good P l) (q : ℕ) [Fact q.Prime] [NeZero q] (hq2 : q ≠ 2)
    (hqnot : q ∉ l) (hfull : geneuclidUnits q l = Finset.univ)
    (hexception : q ≠ 5 ∨ (geneuclidProduct l : ZMod q) ≠ 3) :
    ∃ l', l <+: l' ∧ l.length < l'.length ∧ Good P l' ∧ q ∈ l' := by
  let n : ZMod q := geneuclidProduct l
  have hn0 : n ≠ 0 := geneuclidProduct_ne_zero_mod q l hg.2.2.1 hqnot
  by_cases hchar : geneuclidQuadChar q (-n) = 1
  · exact geneuclid_reach_q_of_char_one P l hg q hqnot hfull hchar
  · obtain ⟨x, hxchar⟩ := geneuclid_character_witness q hq2 n hn0 hexception
    have hxmem : x ∈ geneuclidUnits q l := by simp [hfull]
    obtain ⟨I, hI, hExpr⟩ := geneuclid_unit_expression q l x hxmem
    have hexpr0 : (x : ZMod q) + n / (x : ZMod q) ≠ 0 := by
      intro hz
      have hsquare : IsSquare (-n) := by
        refine ⟨(x : ZMod q), ?_⟩
        field_simp at hz
        linear_combination -hz
      have hqchar : geneuclidQuadChar q (-n) = 1 := by
        change (((quadraticChar (ZMod q)) (-n) : ℤ) : ℂ) = 1
        exact_mod_cast (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hn0)).mpr hsquare
      exact hchar hqchar
    have hm0 : geneuclidN l I ≠ 0 := by
      have hge := euclidN_ge_two l hg.2.2.1 I hI
      simp only [geneuclidN]
      omega
    have hmchar : geneuclidQuadChar q ((geneuclidN l I : ℕ) : ZMod q) ≠ 1 := by
      rw [← hExpr]
      exact hxchar
    obtain ⟨p, hpprime, hpdvd, hpchar⟩ :=
      geneuclid_exists_prime_factor_map_ne_one
        (fun m : ℕ => geneuclidQuadChar q (m : ZMod q)) (by simp)
        (fun a b => by simp) hm0 hmchar
    have hpnot : p ∉ l :=
      fresh_of_dvd_euclid l hg.2.1 hg.2.2.1 I hI p hpprime hpdvd
    have hpq : p ≠ q := by
      intro hpq
      subst p
      have hcast0 : (geneuclidN l I : ZMod q) = 0 :=
        (ZMod.natCast_eq_zero_iff (geneuclidN l I) q).mpr hpdvd
      apply hexpr0
      rw [show n = (geneuclidProduct l : ZMod q) by rfl, hExpr]
      exact hcast0
    let l' := l ++ [p]
    have hg' : Good P l' := good_append P l hg p hpprime hpnot I hI hpdvd
    have hqnot' : q ∉ l' := by simp [l', hqnot, hpq.symm]
    have hfull' : geneuclidUnits q l' = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro u
      apply geneuclidUnits_append_subset q l p
      simp [hfull]
    have hnchar := geneuclidQuadChar_eq_neg_one_of_ne_one q (neg_ne_zero.mpr hn0) hchar
    have hp0 : (p : ZMod q) ≠ 0 := by
      intro hp0
      have hqp : q ∣ p := (ZMod.natCast_eq_zero_iff p q).mp hp0
      exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hpprime).mp hqp).symm
    have hpchar' := geneuclidQuadChar_eq_neg_one_of_ne_one q hp0 hpchar
    have hchar' : geneuclidQuadChar q (-(geneuclidProduct l' : ZMod q)) = 1 := by
      rw [geneuclidProduct_append, Nat.cast_mul]
      rw [← neg_mul]
      change geneuclidQuadChar q (-n * (p : ZMod q)) = 1
      rw [map_mul, hnchar, hpchar']
      norm_num
    obtain ⟨l'', hpref, hlen, hgood, hqmem⟩ :=
      geneuclid_reach_q_of_char_one P l' hg' q hqnot' hfull' hchar'
    exact ⟨l'', (List.prefix_append l [p]).trans hpref,
      lt_trans (by simp [l']) hlen, hgood, hqmem⟩

theorem geneuclid_reach_q_of_full (P : Finset ℕ) (l : List ℕ)
    (hg : Good P l) (q : ℕ) [Fact q.Prime] [NeZero q] (hq2 : q ≠ 2)
    (hqnot : q ∉ l) (hfull : geneuclidUnits q l = Finset.univ) :
    ∃ l', l <+: l' ∧ l.length < l'.length ∧ Good P l' ∧ q ∈ l' := by
  by_cases hexception : q ≠ 5 ∨ (geneuclidProduct l : ZMod q) ≠ 3
  · exact geneuclid_reach_q_of_full_nonexception P l hg q hq2 hqnot hfull hexception
  · push Not at hexception
    obtain ⟨rfl, hn3⟩ := hexception
    let I : Finset ℕ := ∅
    have hI : I ⊆ Finset.range l.length := Finset.empty_subset _
    have hm0 : geneuclidN l I ≠ 0 := by
      have hge := euclidN_ge_two l hg.2.2.1 I hI
      simp only [geneuclidN]
      omega
    have h3zero : (3 : ZMod 5) ≠ 0 := by
      intro h
      have hval := congrArg ZMod.val h
      norm_num [ZMod.val_ofNat, ZMod.val_one] at hval
    have h4zero : (4 : ZMod 5) ≠ 0 := by
      intro h
      have hval := congrArg ZMod.val h
      norm_num [ZMod.val_ofNat] at hval
    have h4one : (4 : ZMod 5) ≠ 1 := by
      intro h
      have hval := congrArg ZMod.val h
      norm_num [ZMod.val_ofNat, ZMod.val_one] at hval
    have hmres : ((geneuclidN l I : ℕ) : ZMod 5) ≠ 1 := by
      change ((1 + geneuclidProduct l : ℕ) : ZMod 5) ≠ 1
      rw [Nat.cast_add, Nat.cast_one, hn3]
      intro h
      apply h4one
      calc
        (4 : ZMod 5) = 1 + 3 := by norm_num
        _ = 1 := h
    have hmres0 : ((geneuclidN l I : ℕ) : ZMod 5) ≠ 0 := by
      change ((1 + geneuclidProduct l : ℕ) : ZMod 5) ≠ 0
      rw [Nat.cast_add, Nat.cast_one, hn3]
      intro h
      apply h4zero
      calc
        (4 : ZMod 5) = 1 + 3 := by norm_num
        _ = 0 := h
    obtain ⟨p, hpprime, hpdvd, hpres⟩ :=
      geneuclid_exists_prime_factor_map_ne_one (fun m : ℕ => (m : ZMod 5))
        (by norm_num) (fun a b => by simp) hm0 hmres
    have hpnot : p ∉ l :=
      fresh_of_dvd_euclid l hg.2.1 hg.2.2.1 I hI p hpprime hpdvd
    have hp5 : p ≠ 5 := by
      intro hp5
      subst p
      apply hmres0
      exact (ZMod.natCast_eq_zero_iff (geneuclidN l I) 5).mpr hpdvd
    let l' := l ++ [p]
    have hg' : Good P l' := good_append P l hg p hpprime hpnot I hI hpdvd
    have h5not' : 5 ∉ l' := by simp [l', hqnot, hp5.symm]
    have hfull' : geneuclidUnits 5 l' = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro u
      apply geneuclidUnits_append_subset 5 l p
      simp [hfull]
    have hn3' : (geneuclidProduct l' : ZMod 5) ≠ 3 := by
      rw [geneuclidProduct_append, Nat.cast_mul, hn3]
      intro h
      apply hpres
      exact mul_left_cancel₀ h3zero h
    obtain ⟨l'', hpref, hlen, hgood, h5mem⟩ :=
      geneuclid_reach_q_of_full_nonexception P l' hg' 5 (by norm_num) h5not' hfull'
        (Or.inr hn3')
    exact ⟨l'', (List.prefix_append l [p]).trans hpref,
      lt_trans (by simp [l']) hlen, hgood, h5mem⟩

/-- From any valid list, one valid step produces a new prime. -/
theorem step_extend (P : Finset ℕ) (l : List ℕ) (hg : Good P l)
    (I : Finset ℕ) (hI : I ⊆ Finset.range l.length) :
    ∃ r, r.Prime ∧ r ∉ l ∧
      r ∣ (∏ i ∈ I, eVal l i) + ∏ i ∈ (Finset.range l.length \ I), eVal l i ∧
      Good P (l ++ [r]) := by
  have hN := euclidN_ge_two l hg.2.2.1 I hI
  obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hN)
  have hrnotin : r ∉ l :=
    fresh_of_dvd_euclid l hg.2.1 hg.2.2.1 I hI r hrprime hrdvd
  exact ⟨r, hrprime, hrnotin, hrdvd, good_append P l hg r hrprime hrnotin I hI hrdvd⟩

/-- Euclid's argument: some prime is always missing. -/
theorem exists_fresh (l : List ℕ) (hnod : l.Nodup) (hprime : ∀ x ∈ l, x.Prime) :
    ∃ r, r.Prime ∧ r ∉ l := by
  have hI : (∅ : Finset ℕ) ⊆ Finset.range l.length := Finset.empty_subset _
  have hN := euclidN_ge_two l hprime ∅ hI
  obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hN)
  exact ⟨r, hrprime, fresh_of_dvd_euclid l hnod hprime ∅ hI r hrprime hrdvd⟩

/-- A product of odd numbers is odd. -/
theorem odd_finset_prod (s : Finset ℕ) (f : ℕ → ℕ) (h : ∀ i ∈ s, Odd (f i)) :
    Odd (∏ i ∈ s, f i) := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    exact odd_one
  | insert a s hnot ihm =>
    rw [Finset.prod_insert hnot]
    exact Odd.mul (h _ (Finset.mem_insert_self _ _))
      (ihm (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- If `2` is missing, one valid step adjoins it (Booker's Proposition, `q = 2`
case: the product of odd primes is odd, so `P + 1` is even). -/
theorem reach_two (P : Finset ℕ) (l : List ℕ) (hg : Good P l) (h2 : 2 ∉ l) :
    ∃ l', l <+: l' ∧ l.length < l'.length ∧ Good P l' ∧ 2 ∈ l' := by
  have hprime : ∀ x ∈ l, x.Prime := hg.2.2.1
  have hodd : ∀ x ∈ l, Odd x := by
    intro x hx
    have hne : x ≠ 2 := fun h => h2 (h ▸ hx)
    exact (hprime x hx).odd_of_ne_two hne
  have hB : Odd (∏ i ∈ Finset.range l.length, eVal l i) := by
    apply odd_finset_prod
    intro i hi
    rw [Finset.mem_range] at hi
    rw [eVal_lt l i hi]
    exact hodd _ (List.getElem_mem hi)
  have hI : (∅ : Finset ℕ) ⊆ Finset.range l.length := Finset.empty_subset _
  have heven : Even ((∏ i ∈ (∅ : Finset ℕ), eVal l i) +
      ∏ i ∈ (Finset.range l.length \ ∅), eVal l i) := by
    rw [Finset.prod_empty, Finset.sdiff_empty]
    exact odd_one.add_odd hB
  have hdvd : 2 ∣ (∏ i ∈ (∅ : Finset ℕ), eVal l i) +
      ∏ i ∈ (Finset.range l.length \ ∅), eVal l i := even_iff_two_dvd.mp heven
  refine ⟨l ++ [2], List.prefix_append l [2], ?_,
    good_append P l hg 2 Nat.prime_two h2 ∅ hI hdvd, by simp⟩
  rw [List.length_append, List.length_singleton]
  exact Nat.lt_succ_self _

theorem reach_odd (P : Finset ℕ) (l : List ℕ) (hg : Good P l)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hmin : ∀ p, p.Prime → p < q → p ∈ l) :
    ∃ l', l <+: l' ∧ l.length < l'.length ∧ Good P l' ∧ q ∈ l' := by
  by_cases hqmem : q ∈ l
  · have hI : (∅ : Finset ℕ) ⊆ Finset.range l.length := Finset.empty_subset _
    obtain ⟨r, _hrprime, _hrnot, _hrdvd, hg'⟩ := step_extend P l hg ∅ hI
    refine ⟨l ++ [r], List.prefix_append l [r], by simp, hg', ?_⟩
    exact List.mem_append.mpr (Or.inl hqmem)
  let _ : Fact q.Prime := ⟨hq⟩
  let _ : NeZero q := ⟨hq.ne_zero⟩
  let deficit (xs : List ℕ) := Fintype.card (ZMod q)ˣ - (geneuclidUnits q xs).card
  generalize hk : deficit l = k
  induction k using Nat.strong_induction_on generalizing l with
  | h k ih =>
      by_cases hqapp : GeneuclidAppendable l q
      · obtain ⟨_hqprime, I, hI, hqdvd⟩ := hqapp
        refine ⟨l ++ [q], List.prefix_append l [q], by simp,
          good_append P l hg q hq hqmem I hI hqdvd, by simp⟩
      · let S := geneuclidUnits q l
        let H := MulAction.stabilizer (ZMod q)ˣ S
        by_cases hgrow : ∃ (p : ℕ) (hp0 : (p : ZMod q) ≠ 0),
            GeneuclidAppendable l p ∧ Units.mk0 (p : ZMod q) hp0 ∉ H
        · obtain ⟨p, hp0, hpapp, hpH⟩ := hgrow
          obtain ⟨hpprime, I, hI, hpdvd⟩ := hpapp
          have hpnot : p ∉ l :=
            fresh_of_dvd_euclid l hg.2.1 hg.2.2.1 I hI p hpprime hpdvd
          have hpq : p ≠ q := by
            intro hpq
            subst p
            exact hqapp ⟨hq, I, hI, hpdvd⟩
          let l' := l ++ [p]
          have hg' : Good P l' := good_append P l hg p hpprime hpnot I hI hpdvd
          have hqmem' : q ∉ l' := by simp [l', hqmem, hpq.symm]
          have hmin' : ∀ r, r.Prime → r < q → r ∈ l' := by
            intro r hr hrq
            exact List.mem_append.mpr (Or.inl (hmin r hr hrq))
          have hsubset : S ⊆ geneuclidUnits q l' := by
            exact geneuclidUnits_append_subset q l p
          have houtside : ∃ u ∈ S,
              u * Units.mk0 (p : ZMod q) hp0 ∉ S := by
            rw [MulAction.mem_stabilizer_finset'] at hpH
            push Not at hpH
            obtain ⟨u, hu, hpu⟩ := hpH
            refine ⟨u, hu, ?_⟩
            simpa [smul_eq_mul, mul_comm] using hpu
          obtain ⟨u, hu, huout⟩ := houtside
          have hunew : u * Units.mk0 (p : ZMod q) hp0 ∈ geneuclidUnits q l' := by
            exact geneuclidUnits_mul_mk0_mem_append q l p hp0 u hu
          have hstrict : S ⊂ geneuclidUnits q l' := by
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨hsubset, ?_⟩
            intro heq
            apply huout
            rwa [heq]
          have hcardlt : S.card < (geneuclidUnits q l').card :=
            Finset.card_lt_card hstrict
          have htotal : (geneuclidUnits q l').card ≤ Fintype.card (ZMod q)ˣ :=
            Finset.card_le_univ _
          have holdtotal : S.card < Fintype.card (ZMod q)ˣ :=
            hcardlt.trans_le htotal
          have hdlt : deficit l' < k := by
            rw [← hk]
            simp only [deficit]
            exact Nat.sub_lt_sub_left holdtotal hcardlt
          obtain ⟨l'', hpref, hlen, hgood, hqmem''⟩ :=
            ih (deficit l') hdlt l' hg' hmin' hqmem' rfl
          exact ⟨l'', (List.prefix_append l [p]).trans hpref,
            lt_trans (by simp [l']) hlen, hgood, hqmem''⟩
        · have hstable : ∀ (p : ℕ) (hp0 : (p : ZMod q) ≠ 0),
              GeneuclidAppendable l p → Units.mk0 (p : ZMod q) hp0 ∈ H := by
            intro p hp0 hpapp
            by_contra hpH
            exact hgrow ⟨p, hp0, hpapp, hpH⟩
          have hfull : geneuclidUnits q l = Finset.univ :=
            geneuclid_stable_units_eq_univ q hq2 l hg.2.2.1 hqmem hmin hqapp hstable
          exact geneuclid_reach_q_of_full P l hg q hq2 hqmem hfull

/-- The smallest missing prime can be adjoined by finitely many valid steps. -/
theorem prop_reach (P : Finset ℕ) (l : List ℕ) (hg : Good P l) :
    ∃ l', l <+: l' ∧ l.length < l'.length ∧ Good P l' ∧
      sInf {p | p.Prime ∧ p ∉ l} ∈ l' := by
  have hne : {p | p.Prime ∧ p ∉ l}.Nonempty := by
    obtain ⟨r, hrp, hrn⟩ := exists_fresh l hg.2.1 hg.2.2.1
    exact ⟨r, hrp, hrn⟩
  have hqP : (sInf {p | p.Prime ∧ p ∉ l}).Prime ∧
      sInf {p | p.Prime ∧ p ∉ l} ∉ l := Nat.sInf_mem hne
  obtain ⟨hqprime, hqnotin⟩ := hqP
  have hmin : ∀ p, p.Prime → p < sInf {p | p.Prime ∧ p ∉ l} → p ∈ l := by
    intro m hmp hmlt
    by_contra hnin
    have hmem : m ∈ {p | p.Prime ∧ p ∉ l} := ⟨hmp, hnin⟩
    have hle := Nat.sInf_le hmem
    omega
  rcases eq_or_ne (sInf {p | p.Prime ∧ p ∉ l}) 2 with h2 | h2
  · obtain ⟨l', hp, hlen, hg', hm⟩ :=
      reach_two P l hg (by rwa [h2] at hqnotin)
    exact ⟨l', hp, hlen, hg', by rwa [h2]⟩
  · obtain ⟨l', hp, hlen, hg', hm⟩ := reach_odd P l hg _ hqprime h2 hmin
    exact ⟨l', hp, hlen, hg', hm⟩

end MetaMathlibExt
