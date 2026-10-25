import Mathlib
import sympy.Basic
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part44
open MetaMathlibExt


namespace MetaMathlibExt

/--
[zagCard_fullCycles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagCard_fullCycles (n : ℕ) (hn : 0 < n) :
  Fintype.card {σ : Equiv.Perm (Fin n) //
    Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = 1} =
    (n - 1).factorial := by
  rw [card_perm_cycleCount_eq_stirlingFirst]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa using Nat.stirlingFirst_one_right m

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zag_card_cycleMinima](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zag_card_cycleMinima {n : ℕ}
  (e π : Equiv.Perm (Fin n)) :
  (zagCycleMinima e π).card = cycleQuotientCount π := by
  rw [cycleQuotientCount,
    Nat.card_congr (zagCycleQuotientEquivMinima e π),
    Nat.card_eq_fintype_card, Fintype.card_coe]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[toFinset_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma ZagMarkedTriple.toFinset_subset {n : ℕ}
  {e π : Equiv.Perm (Fin n)} (m : ZagMarkedTriple e π) :
  m.toFinset ⊆ zagCycleMinima e π := by
  intro x hx
  simp only [ZagMarkedTriple.toFinset, Finset.mem_insert,
    Finset.mem_singleton] at hx
  obtain rfl | rfl | rfl := hx
  · exact m.first_mem
  · exact m.middle_mem
  · exact m.third_mem

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagCard_trivialAntiExceedances](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagCard_trivialAntiExceedances {n : ℕ}
  (e π : Equiv.Perm (Fin n)) :
  Nat.card {x : Fin n // zagTrivialAntiExceedance e π x} =
    cycleQuotientCount π := by
  rw [cycleQuotientCount]
  exact (Nat.card_congr (zagCycleTrivialAntiExceedanceEquiv e π)).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagCard_nontrivialAntiExceedances](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagCard_nontrivialAntiExceedances {n : ℕ}
  (e π : Equiv.Perm (Fin n)) :
  Nat.card {x : Fin n // zagNontrivialAntiExceedance e π x} =
    n - Nat.card {x : Fin n // zagExceedance e π x} -
      cycleQuotientCount π := by
  classical
  have hsplit :
    Nat.card {x : {x : Fin n // ¬zagExceedance e π x} //
      ¬zagTrivialAntiExceedance e π x.1} =
      Nat.card {x : Fin n // ¬zagExceedance e π x} -
        Nat.card {x : {x : Fin n // ¬zagExceedance e π x} //
          zagTrivialAntiExceedance e π x.1} := by
    simp only [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl _
  have hanti :
    Nat.card {x : Fin n // ¬zagExceedance e π x} =
      n - Nat.card {x : Fin n // zagExceedance e π x} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_fin]
  have htrivial :
    Nat.card {x : {x : Fin n // ¬zagExceedance e π x} //
      zagTrivialAntiExceedance e π x.1} = cycleQuotientCount π := by
    calc
      _ = Nat.card {x : Fin n // zagTrivialAntiExceedance e π x} :=
        (Nat.card_congr (zagTrivialAntiExceedanceEquiv e π)).symm
      _ = cycleQuotientCount π := zagCard_trivialAntiExceedances e π
  rw [Nat.card_congr (zagNontrivialAntiExceedanceEquiv e π), hsplit,
    hanti, htrivial]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[root_le_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma ZagOddMarks.root_le_of_mem {n : ℕ}
  {e π : Equiv.Perm (Fin n)} {root x : Fin n}
  (m : ZagOddMarks e π root) (hx : x ∈ m.toList) : root ≤ x := by
  induction m with
  | terminal m =>
    simp only [toList, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain rfl | rfl | rfl := hx
    · exact le_rfl
    · exact m.first_lt_middle.le
    · exact (m.first_lt_middle.trans m.middle_lt_third).le
  | prepend first middle third first_mem middle_mem first_lt_middle
    middle_lt_third tail ih =>
    simp only [toList, List.mem_cons] at hx
    obtain rfl | rfl | hx := hx
    · exact le_rfl
    · exact first_lt_middle.le
    · exact first_lt_middle.le.trans
      (middle_lt_third.le.trans (ih hx))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mem_cycleMinima](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma ZagOddMarks.mem_cycleMinima {n : ℕ}
  {e π : Equiv.Perm (Fin n)} {root x : Fin n}
  (m : ZagOddMarks e π root) (hx : x ∈ m.toList) :
  x ∈ zagCycleMinima e π := by
  induction m with
  | terminal m =>
    simp only [toList, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain rfl | rfl | rfl := hx
    · exact m.first_mem
    · exact m.middle_mem
    · exact m.third_mem
  | prepend first middle third first_mem middle_mem first_lt_middle
    middle_lt_third tail ih =>
    simp only [toList, List.mem_cons] at hx
    obtain rfl | rfl | hx := hx
    · exact first_mem
    · exact middle_mem
    · exact ih hx

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sortedLT_toList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma ZagOddMarks.sortedLT_toList {n : ℕ}
  {e π : Equiv.Perm (Fin n)} {root : Fin n}
  (m : ZagOddMarks e π root) : m.toList.SortedLT := by
  induction m with
  | terminal m =>
    simp [toList, List.sortedLT_cons, List.sortedLT_nil,
      m.first_lt_middle, m.middle_lt_third,
      m.first_lt_middle.trans m.middle_lt_third]
  | prepend first middle third first_mem middle_mem first_lt_middle
    middle_lt_third tail ih =>
    rw [List.sortedLT_iff_pairwise] at ih ⊢
    simp only [toList, List.pairwise_cons]
    refine ⟨?_, ?_, ih⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      obtain rfl | hx := hx
      · exact first_lt_middle
      · exact first_lt_middle.trans
        (middle_lt_third.trans_le (tail.root_le_of_mem hx))
    · intro x hx
      exact middle_lt_third.trans_le (tail.root_le_of_mem hx)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[nodup_toList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma ZagOddMarks.nodup_toList {n : ℕ}
  {e π : Equiv.Perm (Fin n)} {root : Fin n}
  (m : ZagOddMarks e π root) : m.toList.Nodup :=
  m.sortedLT_toList.nodup

end MetaMathlibExt

namespace MetaMathlibExt

/--
[head?_toList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma ZagOddMarks.head?_toList {n : ℕ}
  {e π : Equiv.Perm (Fin n)} {root : Fin n}
  (m : ZagOddMarks e π root) : m.toList.head? = some root := by
  cases m <;> rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagCard_oddMarks_depth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagCard_oddMarks_depth {n : ℕ}
  (e π : Equiv.Perm (Fin n)) (d : ℕ) :
  Nat.card {q : Σ root, ZagOddMarks e π root // q.2.depth = d} =
    (cycleQuotientCount π).choose (2 * d + 3) := by
  rw [Nat.card_congr (zagOddMarksDepthEquivPowerset e π d),
    Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, zag_card_cycleMinima]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagReverseIndex_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagReverseIndex_lt {n : ℕ} (hn : 0 < n)
  (a b : Fin n) :
  -(finRotate n a) < -b ↔ ¬a < b ∧ b.val ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  cases m with
  | zero =>
    have ha : a = ⟨0, by omega⟩ := Subsingleton.elim _ _
    have hb : b = ⟨0, by omega⟩ := Subsingleton.elim _ _
    subst a
    subst b
    simp
  | succ m =>
    let hNeZero : NeZero (m + 2) := ⟨by omega⟩
    simp only [Fin.lt_def, Fin.val_neg', finRotate_apply,
      Fin.val_add, Fin.val_one]
    change ((m + 2) - (a.val + 1) % (m + 2)) % (m + 2) <
      ((m + 2) - b.val) % (m + 2) ↔
      ¬a.val < b.val ∧ b.val ≠ 0
    by_cases ha : a.val + 1 = m + 2
    · have hmoda : (a.val + 1) % (m + 2) = 0 := by
      rw [ha, Nat.mod_self]
      rw [hmoda]
      simp only [Nat.sub_zero, Nat.mod_self, zero_lt_iff]
      by_cases hb : b.val = 0
      · simp [hb]
      · have hbpos : 0 < b.val := Nat.pos_of_ne_zero hb
        have hsubpos : 0 < (m + 2) - b.val := by omega
        have hsublt : (m + 2) - b.val < m + 2 := by omega
        rw [Nat.mod_eq_of_lt hsublt]
        constructor
        · intro _hleft
          exact ⟨by omega, hb⟩
        · intro _hright
          exact hsubpos.ne'
    · have halt : a.val + 1 < m + 2 := by omega
      rw [Nat.mod_eq_of_lt halt]
      have hleftlt : (m + 2) - (a.val + 1) < m + 2 := by omega
      rw [Nat.mod_eq_of_lt hleftlt]
      by_cases hb : b.val = 0
      · simp [hb, Nat.mod_self]
      · have hsublt : (m + 2) - b.val < m + 2 := by omega
        rw [Nat.mod_eq_of_lt hsublt]
        constructor
        · intro h
          exact ⟨by omega, hb⟩
        · rintro ⟨hab, -⟩
          omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagHorizontal_apply_order](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagHorizontal_apply_order {n : ℕ}
  (e : Equiv.Perm (Fin n)) (x : Fin n) :
  e.symm (zagHorizontal e x) = finRotate n (e.symm x) := by
  simp [zagHorizontal, Equiv.Perm.mul_apply]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagReflectedVertical_apply_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagReflectedVertical_apply_horizontal {n : ℕ}
  (e π : Equiv.Perm (Fin n)) (x : Fin n) :
  (zagDiagonal e π)⁻¹ (zagHorizontal e x) = π x := by
  have h : (zagDiagonal e π)⁻¹ * zagHorizontal e = π := by
    simp only [zagDiagonal, mul_inv_rev, inv_inv]
    group
  exact congrArg (fun f : Equiv.Perm (Fin n) => f x) h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[depth_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma ZagOddMarks.depth_lt {n : ℕ}
  {e π : Equiv.Perm (Fin n)} {root : Fin n}
  (m : ZagOddMarks e π root) : m.depth < n := by
  have hlen := m.nodup_toList.length_le_card
  rw [m.length_toList, Fintype.card_fin] at hlen
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagCard_originalTotal_eq_sum_depth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagCard_originalTotal_eq_sum_depth
  (n k l : ℕ) (hn : 0 < n) :
  Nat.card (ZagOriginalTotal n hn k l) =
    ∑ d : Fin n,
      (k + 2 * (d.val + 1)).choose (2 * d.val + 3) *
        Nat.card (ZagPlaneConfigBy n hn (k + 2 * (d.val + 1)) l) := by
  classical
  let E := (zagOriginalTotalEquivPointedConfigBy n hn k l).trans
    ((zagPointedConfigByEquivOddMarkedConfigBy n hn k l).trans
      (zagOddMarkedConfigByEquivDepthDecomposition n hn k l))
  rw [Nat.card_congr E, Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.card_sigma]
  have hmarks (q : ZagPlaneConfigBy n hn (k + 2 * (d.val + 1)) l) :
    Nat.card {m : Σ root, ZagOddMarks q.1.1.1 q.1.2 root //
      m.2.depth = d.val} =
      (k + 2 * (d.val + 1)).choose (2 * d.val + 3) := by
    rw [zagCard_oddMarks_depth, q.2.1]
  simp_rw [hmarks]
  rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
    Nat.card_eq_fintype_card, Nat.mul_comm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagCard_planeConfigDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagCard_planeConfigDiagonal
  (n k : ℕ) (hn : 0 < n) :
  Nat.card (ZagPlaneConfigDiagonal n hn k) =
    (n - 1).factorial * Nat.stirlingFirst n k := by
  rw [Nat.card_congr (zagPlaneConfigDiagonalEquivProduct n k hn), Nat.card_prod]
  have horder : Nat.card (ZagAnchoredOrder n hn) = (n - 1).factorial := by
    rw [Nat.card_congr (zagAnchoredOrderEquivFullCycle n hn),
      Nat.card_eq_fintype_card]
    simpa only [cycleQuotientCount_eq] using zagCard_fullCycles n hn
  have hcycles :
    Fintype.card {D : Equiv.Perm (Fin n) // cycleQuotientCount D = k} =
      Nat.stirlingFirst n k := by
    simpa only [cycleQuotientCount_eq] using card_perm_cycleCount_eq_stirlingFirst n k
  rw [horder, Nat.card_eq_fintype_card, hcycles]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagCard_planeConfigDiagonal_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagCard_planeConfigDiagonal_decompose
  (n k : ℕ) (hn : 0 < n) (hparity : Even (n - k)) :
  Nat.card (ZagPlaneConfigDiagonal n hn k) =
    Nat.card (ZagPlaneConfigBy n hn 1 k) +
      ∑ d : Fin n, Nat.card (ZagPlaneConfigBy n hn (2 * d.val + 3) k) := by
  let E := zagOddVerticalDecompositionEquiv n k hn hparity
  rw [← Nat.card_congr E, Nat.card_sum, Nat.card_sigma]
  have hcard (j : ℕ) :
    Nat.card (ZagVerticalFiber n hn k j) =
      Nat.card (ZagPlaneConfigBy n hn j k) :=
    (Nat.card_congr (zagPlaneConfigByEquivVerticalFiber n hn j k)).symm
  rw [hcard]
  simp_rw [hcard]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagCard_reflectedTotal_eq_sum_depth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagCard_reflectedTotal_eq_sum_depth
  (n k : ℕ) (hn : 0 < n) :
  Nat.card (ZagReflectedTotal n hn k) =
    ∑ d : Fin n,
      Nat.card (ZagPlaneConfigBy n hn (2 * d.val + 3) k) := by
  rw [Nat.card_congr (zagReflectedTotalEquivOriginalTotal n k hn),
    zagCard_originalTotal_eq_sum_depth]
  apply Finset.sum_congr rfl
  intro d hd
  have hindex : 1 + 2 * (d.val + 1) = 2 * d.val + 3 := by omega
  rw [hindex, Nat.choose_self, one_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagStirlingPolynomial_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagStirlingPolynomial_coeff (n k : ℕ) :
  (zagStirlingPolynomial n).coeff k = (Nat.stirlingFirst n k : ℤ) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [zagStirlingPolynomial]
    | succ k => simp [zagStirlingPolynomial, Polynomial.coeff_one]
  | succ n ih =>
    cases k with
    | zero =>
      rw [zagStirlingPolynomial, Finset.prod_range_succ]
      change ((zagStirlingPolynomial n) *
        (Polynomial.X + Polynomial.C (n : ℤ))).coeff 0 = _
      rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul,
        ← Polynomial.coeff_zero_eq_eval_zero, ih]
      cases n <;> simp
    | succ k =>
      rw [zagStirlingPolynomial, Finset.prod_range_succ]
      change ((zagStirlingPolynomial n) *
        (Polynomial.X + Polynomial.C (n : ℤ))).coeff (k + 1) = _
      rw [mul_add, Polynomial.coeff_add, Polynomial.coeff_mul_X,
        Polynomial.coeff_mul_C, ih, ih, Nat.stirlingFirst_succ_succ]
      push_cast
      ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagStirlingPolynomial_natDegree_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagStirlingPolynomial_natDegree_le (n : ℕ) :
  (zagStirlingPolynomial n).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rwa [zagStirlingPolynomial_coeff, Nat.stirlingFirst_eq_zero_of_lt hk]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagStirlingPolynomial_taylor_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagStirlingPolynomial_taylor_coeff (n k : ℕ) (a : ℤ) :
  (Polynomial.taylor a (zagStirlingPolynomial n)).coeff k =
    ∑ m ∈ Finset.range (n + 1),
      ((m + k).choose k : ℤ) * (Nat.stirlingFirst n (m + k) : ℤ) * a ^ m := by
  rw [Polynomial.taylor_coeff]
  have hdegree := Polynomial.natDegree_hasseDeriv_le (zagStirlingPolynomial n) k
  have hrange : (Polynomial.hasseDeriv k (zagStirlingPolynomial n)).natDegree < n + 1 := by
    have hp := zagStirlingPolynomial_natDegree_le n
    omega
  rw [Polynomial.eval_eq_sum_range' hrange]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.hasseDeriv_coeff, zagStirlingPolynomial_coeff]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagOddDifferenceSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagOddDifferenceSum (n : ℕ) (A : ℕ → ℤ)
  (hzero : ∀ d < n + 1, n + 2 ≤ 2 * d + 1 → A (2 * d + 1) = 0) :
  (∑ m ∈ Finset.range (n + 2), A m * (1 - (-1 : ℤ) ^ m)) =
    2 * ∑ d : Fin (n + 1), A (2 * d.val + 1) := by
  classical
  let s := (Finset.range (n + 2)).filter Odd
  let t := (Finset.range (n + 1)).filter fun d => 2 * d + 1 < n + 2
  have heven :
    ∑ m ∈ (Finset.range (n + 2)).filter (fun m => ¬Odd m),
      A m * (1 - (-1 : ℤ) ^ m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have hmEven : Even m := Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hm).2
    rw [hmEven.neg_one_pow, sub_self, mul_zero]
  have hodd :
    ∑ m ∈ s, A m = ∑ d ∈ t, A (2 * d + 1) := by
    apply Finset.sum_bij (fun m _ => m / 2)
    · intro m hm
      have hmRange := (Finset.mem_filter.mp hm).1
      have hmLt := Finset.mem_range.mp hmRange
      have hmOdd := (Finset.mem_filter.mp hm).2
      have hmEq := Nat.two_mul_div_two_add_one_of_odd hmOdd
      rw [two_mul] at hmEq
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        omega
      · rw [two_mul, hmEq]
        exact hmLt
    · intro a ha b hb hab
      have haEq := Nat.two_mul_div_two_add_one_of_odd (Finset.mem_filter.mp ha).2
      have hbEq := Nat.two_mul_div_two_add_one_of_odd (Finset.mem_filter.mp hb).2
      omega
    · intro d hd
      have hdRange := (Finset.mem_filter.mp hd).1
      have hdBound := (Finset.mem_filter.mp hd).2
      refine ⟨2 * d + 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdBound, ?_⟩, ?_⟩
      · exact ⟨d, by omega⟩
      · omega
    · intro m hm
      have hmEq := Nat.two_mul_div_two_add_one_of_odd (Finset.mem_filter.mp hm).2
      rw [hmEq]
  have htail :
    ∑ d ∈ t, A (2 * d + 1) =
      ∑ d ∈ Finset.range (n + 1), A (2 * d + 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1))
      (fun d => 2 * d + 1 < n + 2) (fun d => A (2 * d + 1))]
    change ∑ d ∈ t, A (2 * d + 1) =
      ∑ d ∈ t, A (2 * d + 1) +
        ∑ d ∈ (Finset.range (n + 1)).filter (fun d => ¬2 * d + 1 < n + 2),
          A (2 * d + 1)
    have hz :
      ∑ d ∈ (Finset.range (n + 1)).filter (fun d => ¬2 * d + 1 < n + 2),
        A (2 * d + 1) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hdNot := (Finset.mem_filter.mp hd).2
      exact hzero d (Finset.mem_range.mp (Finset.mem_filter.mp hd).1)
        (by rw [two_mul] at hdNot ⊢; omega)
    rw [hz, add_zero]
  calc
    _ = (∑ m ∈ s, A m * (1 - (-1 : ℤ) ^ m)) + 0 := by
      rw [← heven, Finset.sum_filter_add_sum_filter_not]
    _ = ∑ m ∈ s, 2 * A m := by
      simp only [add_zero]
      apply Finset.sum_congr rfl
      intro m hm
      have hmOdd := (Finset.mem_filter.mp hm).2
      rw [hmOdd.neg_one_pow]
      ring
    _ = 2 * ∑ m ∈ s, A m := by rw [Finset.mul_sum]
    _ = 2 * ∑ d ∈ t, A (2 * d + 1) := by rw [hodd]
    _ = 2 * ∑ d ∈ Finset.range (n + 1), A (2 * d + 1) := by rw [htail]
    _ = 2 * ∑ d : Fin (n + 1), A (2 * d.val + 1) := by
      rw [Finset.sum_range]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagStirlingPolynomial_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagStirlingPolynomial_succ (n : ℕ) :
  zagStirlingPolynomial (n + 1) =
    zagStirlingPolynomial n * (Polynomial.X + Polynomial.C (n : ℤ)) := by
  rw [zagStirlingPolynomial, Finset.prod_range_succ]
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagStirlingPolynomial_taylor_one_two_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagStirlingPolynomial_taylor_one_two_step (m : ℕ) :
  Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial (m + 2)) =
    Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m) *
      (Polynomial.X + Polynomial.C (m + 1 : ℤ)) *
      (Polynomial.X + Polynomial.C (m + 2 : ℤ)) := by
  rw [show m + 2 = (m + 1) + 1 by omega, zagStirlingPolynomial_succ,
    zagStirlingPolynomial_succ]
  simp only [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp]
  push_cast
  simp only [Polynomial.C_add, Polynomial.C_1, Polynomial.C_ofNat]
  ring_nf

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagStirlingPolynomial_taylor_neg_one_two_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagStirlingPolynomial_taylor_neg_one_two_step (m : ℕ) :
  Polynomial.taylor (-1 : ℤ) (zagStirlingPolynomial (m + 2)) =
    (Polynomial.X - Polynomial.C 1) * Polynomial.X *
      Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m) := by
  induction m with
  | zero =>
    norm_num [zagStirlingPolynomial, Finset.prod_range_succ, Polynomial.taylor_apply]
    ring_nf
  | succ m ih =>
    conv_lhs =>
      rw [show m + 1 + 2 = (m + 2) + 1 by omega, zagStirlingPolynomial_succ]
    conv_rhs =>
      rw [zagStirlingPolynomial_succ]
    simp only [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.add_comp,
      Polynomial.X_comp, Polynomial.C_comp] at ih ⊢
    rw [ih]
    push_cast
    simp only [Polynomial.C_add, Polynomial.C_neg, Polynomial.C_1,
      Polynomial.C_ofNat]
    ring_nf

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagStirlingPolynomial_taylor_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagStirlingPolynomial_taylor_sub (m : ℕ) :
  Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial (m + 2)) -
    Polynomial.taylor (-1 : ℤ) (zagStirlingPolynomial (m + 2)) =
    Polynomial.C (m + 2 : ℤ) *
      (Polynomial.C 2 * Polynomial.X + Polynomial.C (m + 1 : ℤ)) *
      Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m) := by
  rw [zagStirlingPolynomial_taylor_one_two_step,
    zagStirlingPolynomial_taylor_neg_one_two_step]
  simp only [Polynomial.C_add, Polynomial.C_1, Polynomial.C_ofNat]
  ring_nf

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagX_mul_stirlingPolynomial_taylor_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagX_mul_stirlingPolynomial_taylor_one (m : ℕ) :
  Polynomial.X * Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m) =
    zagStirlingPolynomial (m + 1) := by
  induction m with
  | zero => simp [zagStirlingPolynomial, Polynomial.taylor_apply]
  | succ m ih =>
    rw [zagStirlingPolynomial_succ]
    simp only [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.add_comp,
      Polynomial.X_comp, Polynomial.C_comp] at ih ⊢
    rw [← mul_assoc, ih]
    conv_rhs =>
      rw [show m + 1 + 1 = (m + 1) + 1 by rfl, zagStirlingPolynomial_succ]
    push_cast
    simp only [Polynomial.C_add, Polynomial.C_1]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagStirlingPolynomial_taylor_one_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagStirlingPolynomial_taylor_one_coeff (m k : ℕ) :
  (Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m)).coeff k =
    (Nat.stirlingFirst (m + 1) (k + 1) : ℤ) := by
  calc
    _ = (Polynomial.X *
      Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m)).coeff (k + 1) :=
      (Polynomial.coeff_X_mul _ k).symm
    _ = (zagStirlingPolynomial (m + 1)).coeff (k + 1) := by
      rw [zagX_mul_stirlingPolynomial_taylor_one]
    _ = _ := zagStirlingPolynomial_coeff _ _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagStirlingPolynomial_taylor_sub_coeff_rhs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagStirlingPolynomial_taylor_sub_coeff_rhs (m k : ℕ) :
  (Polynomial.C (m + 2 : ℤ) *
    (Polynomial.C 2 * Polynomial.X + Polynomial.C (m + 1 : ℤ)) *
    Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m)).coeff k =
    (m + 2 : ℤ) *
      (2 * (Nat.stirlingFirst (m + 1) k : ℤ) +
        (m + 1 : ℤ) * (Nat.stirlingFirst (m + 1) (k + 1) : ℤ)) := by
  have hpoly :
    Polynomial.C (m + 2 : ℤ) *
      (Polynomial.C 2 * Polynomial.X + Polynomial.C (m + 1 : ℤ)) *
      Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m) =
      Polynomial.C (m + 2 : ℤ) *
        (Polynomial.C 2 * zagStirlingPolynomial (m + 1) +
          Polynomial.C (m + 1 : ℤ) *
            Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m)) := by
    rw [← zagX_mul_stirlingPolynomial_taylor_one m]
    ring
  rw [hpoly, Polynomial.coeff_C_mul, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, zagStirlingPolynomial_coeff,
    zagStirlingPolynomial_taylor_one_coeff]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagStirlingPolynomial_taylor_sub_coeff_lhs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagStirlingPolynomial_taylor_sub_coeff_lhs
  (m k : ℕ) (hk : 0 < k) :
  (Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial (m + 2)) -
    Polynomial.taylor (-1 : ℤ) (zagStirlingPolynomial (m + 2))).coeff (k - 1) =
    2 * ((k : ℤ) * (Nat.stirlingFirst (m + 2) k : ℤ) +
      ∑ d : Fin (m + 1),
        ((k + 2 * (d.val + 1)).choose (k - 1) : ℤ) *
          (Nat.stirlingFirst (m + 2) (k + 2 * (d.val + 1)) : ℤ)) := by
  let A : ℕ → ℤ := fun r =>
    ((r + (k - 1)).choose (k - 1) : ℤ) *
      (Nat.stirlingFirst (m + 2) (r + (k - 1)) : ℤ)
  have hzero : ∀ d < m + 1 + 1, m + 1 + 2 ≤ 2 * d + 1 → A (2 * d + 1) = 0 := by
    intro d hd hdLarge
    have hlt : m + 2 < 2 * d + 1 + (k - 1) := by omega
    simp only [A, Nat.stirlingFirst_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]
  have hdiff := zagOddDifferenceSum (m + 1) A hzero
  rw [Polynomial.coeff_sub, zagStirlingPolynomial_taylor_coeff,
    zagStirlingPolynomial_taylor_coeff, ← Finset.sum_sub_distrib]
  have hsum :
    (∑ x ∈ Finset.range (m + 2 + 1),
      (((x + (k - 1)).choose (k - 1) : ℤ) *
        (Nat.stirlingFirst (m + 2) (x + (k - 1)) : ℤ) * 1 ^ x -
        ((x + (k - 1)).choose (k - 1) : ℤ) *
          (Nat.stirlingFirst (m + 2) (x + (k - 1)) : ℤ) * (-1) ^ x)) =
      ∑ x ∈ Finset.range (m + 1 + 2), A x * (1 - (-1) ^ x) := by
    apply Finset.sum_congr
    · congr
    · intro x hx
      dsimp only [A]
      simp only [one_pow]
      ring
  rw [hsum, hdiff]
  rw [Fin.sum_univ_succ]
  have hhead : A 1 = (k : ℤ) * (Nat.stirlingFirst (m + 2) k : ℤ) := by
    have hkEq : 1 + (k - 1) = k := by omega
    have hkSucc : (k - 1) + 1 = k := by omega
    have hchoose : k.choose (k - 1) = k := by
      calc
        _ = ((k - 1) + 1).choose (k - 1) := by rw [hkSucc]
        _ = (k - 1) + 1 := Nat.choose_succ_self_right (k - 1)
        _ = k := hkSucc
    dsimp only [A]
    rw [hkEq, hchoose]
  simp only [Fin.val_zero, mul_zero, zero_add, Fin.val_succ]
  rw [hhead]
  apply congrArg (fun z : ℤ => 2 * z)
  apply congrArg (fun z : ℤ =>
    (k : ℤ) * (Nat.stirlingFirst (m + 2) k : ℤ) + z)
  apply Finset.sum_congr rfl
  intro d hd
  dsimp only [A]
  have hindex : 2 * (d.val + 1) + 1 + (k - 1) =
    k + 2 * (d.val + 1) := by omega
  rw [hindex]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagTwo_mul_choose_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagTwo_mul_choose_two (n : ℕ) :
  2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    cases n with
    | zero => simp
    | succ m =>
      rw [Nat.succ_sub_one] at ih
      simp only [Nat.succ_sub_one]
      nlinarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zagStirlingFirst_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagStirlingFirst_recurrence
  (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n) :
  (n + 1 - k) * Nat.stirlingFirst (n + 1) k =
    (∑ d : Fin n,
      (k + 2 * (d.val + 1)).choose (k - 1) *
        Nat.stirlingFirst (n + 1) (k + 2 * (d.val + 1))) +
      (n + 1).choose 2 * Nat.stirlingFirst n k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hpoly := congrArg (fun p : Polynomial ℤ => p.coeff (k - 1))
    (zagStirlingPolynomial_taylor_sub m)
  rw [zagStirlingPolynomial_taylor_sub_coeff_lhs m k hk,
    zagStirlingPolynomial_taylor_sub_coeff_rhs] at hpoly
  norm_cast at hpoly
  have hkSucc : (k - 1) + 1 = k := by omega
  rw [hkSucc] at hpoly
  have hstirling : Nat.stirlingFirst (m + 1 + 1) k =
    (m + 1) * Nat.stirlingFirst (m + 1) k +
      Nat.stirlingFirst (m + 1) (k - 1) := by
    calc
      _ = Nat.stirlingFirst (m + 1 + 1) ((k - 1) + 1) := by rw [hkSucc]
      _ = (m + 1) * Nat.stirlingFirst (m + 1) ((k - 1) + 1) +
        Nat.stirlingFirst (m + 1) (k - 1) :=
        Nat.stirlingFirst_succ_succ (m + 1) (k - 1)
      _ = _ := by rw [hkSucc]
  have hchoose := zagTwo_mul_choose_two (m + 1 + 1)
  rw [Nat.succ_sub_one] at hchoose
  have hsub : m + 1 + 1 - k + k = m + 1 + 1 := by omega
  nlinarith

end MetaMathlibExt

/--
[zagier_probability_product_two_cyclic_permutations](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean)
-/
@[path]
private lemma zagier_probability_product_two_cyclic_permutations_eq
  {n k : ℕ}
-- given
  (hn : 0 < n)
  (hk : 0 < k)
  (hkn : k ≤ n) :
-- imply
  ((Fintype.card {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
    Multiset.card p.1.cycleType + Fintype.card (Function.fixedPoints p.1) = 1 ∧
    Multiset.card p.2.cycleType + Fintype.card (Function.fixedPoints p.2) = 1 ∧
    Multiset.card (p.1 * p.2).cycleType +
    Fintype.card (Function.fixedPoints (p.1 * p.2)) = k}) : ℚ) /
    ((Fintype.card {σ : Equiv.Perm (Fin n) //
    Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = 1}) : ℚ) ^ 2 =
    (1 + (-1 : ℚ) ^ (n - k)) / Nat.factorial (n + 1) *
    Nat.stirlingFirst (n + 1) k := by
-- proof
  apply MetaMathlibExt.zagier_probability_product_two_cyclic_permutations n k hn hk hkn


-- created on 2026-10-20
-- updated on 2026-10-23
