/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Def.Combinatorics.Young.LittlewoodRichardson.Part14
open Finset Function BigOperators Polynomial MvPolynomial

/-!
# The Littlewood-Richardson Rule

This file formalizes the Littlewood-Richardson rule for Schur polynomials, following
the presentation in the Algebraic Combinatorics textbook.

The Littlewood-Richardson rule is one of the most famous results in the theory of symmetric
polynomials. It provides a combinatorial formula for expanding the product of Schur polynomials
as a sum of Schur polynomials:
$$s_\nu \cdot s_{\lambda/\mu} = \sum_{T} s_{\nu + \operatorname{cont}(T)}$$
where the sum is over all ν-Yamanouchi semistandard tableaux T of shape λ/μ.

## Main definitions

* `NPartition`: An N-partition is a weakly decreasing N-tuple of natural numbers
* `contentTableau`: The content of a tableau (counting occurrences of each entry)
* `colGeq`: Restriction of a tableau to columns ≥ j
* `IsYamanouchi`: A semistandard tableau is ν-Yamanouchi if certain conditions hold
* `alternant`: The alternant polynomial a_α
* `schurPoly`: The Schur polynomial s_λ (via the Jacobi-Trudi formula)
* `skewSchurPoly`: The skew Schur polynomial s_{λ/μ}

## Main results

* `littlewoodRichardson`: Zelevinsky's generalized Littlewood-Richardson rule (thm.sf.lr-zy)
* `stembridgeLemma`: Stembridge's lemma (lem.sf.stemb-lem)
* `schurPoly_eq_alternant_div`: Theorem relating Schur polynomials to alternants (thm.sf.schur-symm (b))

## Indexing Convention

**This file uses 1-indexed columns** for skew Young diagrams, matching the textbook convention:
- A cell (i, j) is in Y(λ/μ) iff μ_i < j ≤ λ_i
- Column indices start at 1 (the first column is j = 1)

This differs from `SchurBasics.lean` which uses **0-indexed columns** (Mathlib convention):
- A cell (i, j) is in Y(λ/μ) iff μ_i ≤ j < λ_i
- Column indices start at 0 (the first column is j = 0)

The bijection (i, j) ↔ (i, j+1) converts between the conventions.
See `SchurBasics.skewCellEquiv` and `SchurBasics.mem_skewYoungDiagram_iff_mem_LR_shifted`
for explicit equivalences.

## References

* [Stembridge, *A concise proof of the Littlewood-Richardson rule*][Stembr02]
* [Grinberg-Reiner, *Hopf algebras in Combinatorics*][GriRei]

## Tags

Littlewood-Richardson rule, Schur polynomial, Yamanouchi tableau, symmetric polynomial
-/


namespace AlgebraicCombinatorics

variable {R : Type*} [CommRing R]

variable {N : ℕ}

/-! ### Count swap lemmas for benderKnuthPrefixMatching

After applying `benderKnuthPrefixMatching`, the counts of free k's and free (k+1)'s swap.
These are the prefix-restricted versions of `freeKCount_benderKnuth` and `freeKSuccCount_benderKnuth`.

**Key results** (now proved):
- `freeKCountPrefix_benderKnuthPrefixMatching`: freeKCountPrefix T' = freeKSuccCountPrefix T
- `freeKSuccCountPrefix_benderKnuthPrefixMatching`: freeKSuccCountPrefix T' = freeKCountPrefix T

These lemmas, combined with the cardinality lemmas in the previous section, are used in
`benderKnuthPrefixMatching_involutive_stembridge`. -/
/-! ### Helper lemmas for the involution proof

The following helper lemmas establish the counting arguments needed to prove
`benderKnuthPrefixMatching_involutive_stembridge`. The key insight is that
the counts swap under the transformation:
- `freeKCountPrefix T' = freeKSuccCountPrefix T`
- `freeKSuccCountPrefix T' = freeKCountPrefix T`

These lemmas are analogous to `unmatched_k_becomes_unmatched_kSucc'` for the
full-row version, but restricted to the prefix (columns < j). -/
/-! ## Helper lemmas for Stembridge's involution

The following lemmas establish the key properties needed for defining
and proving properties of Stembridge's involution. -/


/-- If α is not an N-partition, then there exists a misstep index. -/
theorem not_isNPartition_iff_exists_misstep (α : Fin N → ℕ) :
    ¬IsNPartition α ↔ ∃ k : Fin N, isMisstep α k := by
  simp only [_root_.IsNPartition, isMisstep]
  push Not
  constructor
  · intro ⟨i, j, hij, hαij⟩
    -- We have α j > α i with i ≤ j
    -- First handle the case i = j (which is impossible given hαij)
    have hne : i ≠ j := by
      intro heq
      subst heq
      omega
    have hlt : i < j := lt_of_le_of_ne hij hne
    -- Use well-founded induction on j.val - i.val to find a consecutive increase
    have hpos : 0 < j.val - i.val := by
      simp only [Fin.lt_def] at hlt
      omega
    generalize hd : j.val - i.val = d at hpos
    induction d using Nat.strong_induction_on generalizing i j with
    | _ d ih =>
      by_cases hcons : d = 1
      · -- Consecutive case: j.val = i.val + 1
        have hj_eq : j.val = i.val + 1 := by omega
        refine ⟨i, ?_, ?_⟩
        · have : j.val < N := j.isLt
          omega
        · convert hαij using 1
          congr 1
          ext
          exact hj_eq.symm
      · -- Non-consecutive case: d ≥ 2, check the middle
        have hd_ge_2 : d ≥ 2 := by omega
        have hmid_lt_N : i.val + 1 < N := by
          have : j.val < N := j.isLt
          omega
        let mid : Fin N := ⟨i.val + 1, hmid_lt_N⟩
        by_cases hcmp : α i < α mid
        · -- Found consecutive increase at i
          exact ⟨i, hmid_lt_N, by convert hcmp using 1⟩
        · -- α mid ≤ α i, so α mid < α j
          push Not at hcmp
          have hmid_lt_j : α mid < α j := Nat.lt_of_le_of_lt hcmp hαij
          have hmid_le_j : mid ≤ j := by simp only [Fin.le_def, mid]; omega
          have hmid_ne_j : mid ≠ j := by simp only [ne_eq, Fin.ext_iff, mid]; omega
          have hmid_lt : mid < j := lt_of_le_of_ne hmid_le_j hmid_ne_j
          have hdiff : j.val - mid.val = d - 1 := by simp only [mid]; omega
          have hdiff_pos : 0 < d - 1 := by omega
          have hdiff_lt : d - 1 < d := by omega
          exact ih (d - 1) hdiff_lt mid j hmid_le_j hmid_lt_j hmid_ne_j hmid_lt hdiff hdiff_pos
  · intro ⟨k, hk, hαk⟩
    use k, ⟨k.val + 1, hk⟩
    constructor
    · simp only [Fin.le_def]; omega
    · exact Nat.lt_of_lt_of_le hαk (le_refl _)

/-- A semistandard tableau T is not ν-Yamanouchi iff it's not semistandard or
    there exists j > 0 such that ν + cont(col_{≥j}(T)) is not an N-partition. -/
theorem not_isYamanouchi_iff {lam mu : Fin N → ℕ} {nu : Fin N → ℕ} {T : Tableau lam mu} :
    ¬IsYamanouchi nu T ↔
    ¬IsSemistandard T ∨ ∃ j : ℕ, j > 0 ∧ ¬IsNPartition (nu + contentColGeq T j) := by
  simp only [IsYamanouchi, not_and_or]
  constructor
  · intro h
    cases h with
    | inl hnotSS => left; exact hnotSS
    | inr hnotPart =>
      right
      push Not at hnotPart
      exact hnotPart
  · intro h
    cases h with
    | inl hnotSS => left; exact hnotSS
    | inr hex =>
      right
      push Not
      exact hex

/-- For a semistandard tableau T that is not ν-Yamanouchi, the violator columns set is nonempty. -/
theorem violatorColumns_nonempty_of_not_yamanouchi {lam mu : Fin N → ℕ} {nu : Fin N → ℕ}
    {T : Tableau lam mu} (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    (violatorColumns nu T).Nonempty := by
  rw [not_isYamanouchi_iff] at hnotYam
  cases hnotYam with
  | inl hnotSS => exact absurd hT hnotSS
  | inr hex =>
    obtain ⟨j, hj_pos, hnotPart⟩ := hex
    unfold violatorColumns
    simp only [Finset.filter_nonempty_iff]
    -- We need to show j is in the range and satisfies the filter condition
    let maxCol := Finset.sup Finset.univ lam
    by_cases hj_le : j ≤ maxCol + 1
    · use j
      constructor
      · exact Finset.mem_range.mpr (Nat.lt_add_one_of_le hj_le)
      · exact ⟨hj_pos, by simp only [isPartitionAtColumn]; exact hnotPart⟩
    · -- j > maxCol + 1, so contentColGeq T j = 0
      -- Use j' = maxCol + 1 instead, which is in the range
      push Not at hj_le
      use maxCol + 1
      constructor
      · exact Finset.mem_range.mpr (Nat.lt_add_one_of_le (le_refl _))
      · constructor
        · omega
        · simp only [isPartitionAtColumn]
          -- contentColGeq T (maxCol + 1) = 0 since maxCol + 1 > all column indices
          have hzero : contentColGeq T (maxCol + 1) = 0 := by
            apply contentColGeq_eq_zero_of_large
            intro i
            exact Nat.lt_add_one_of_le (Finset.le_sup (Finset.mem_univ i))
          rw [hzero, add_zero]
          -- Now we need to show nu is not an N-partition
          -- Since j > maxCol + 1, contentColGeq T j = 0 as well
          have hzero_j : contentColGeq T j = 0 := by
            apply contentColGeq_eq_zero_of_large
            intro i
            calc lam i ≤ maxCol := Finset.le_sup (Finset.mem_univ i)
              _ < maxCol + 1 := Nat.lt_succ_self _
              _ < j := hj_le
          rw [hzero_j, add_zero] at hnotPart
          exact hnotPart

/-- The misstep set is nonempty when the tuple is not a partition. -/
theorem misstepSet_nonempty_of_not_partition {α : Fin N → ℕ} (h : ¬IsNPartition α) :
    (misstepSet α).Nonempty := by
  rw [not_isNPartition_iff_exists_misstep] at h
  obtain ⟨k, hk⟩ := h
  use k
  simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hk

end AlgebraicCombinatorics
