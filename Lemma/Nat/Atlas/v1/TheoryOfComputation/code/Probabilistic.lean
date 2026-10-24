import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Probabilistic
open Probabilistic TuringMachine BranchingPrograms
open TuringMachine


namespace Probabilistic

/--
[polynomial_roots_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma polynomial_roots_le_degree
  [Field F]
  {p : F[X]}
-- given
  (hp : p ≠ 0) :
-- imply
  (Multiset.card (p.roots) : WithBot ℕ) ≤ p.degree :=
-- proof
  Polynomial.card_roots hp

end Probabilistic

namespace Probabilistic

/--
[distinct_poly_agree_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma distinct_poly_agree_le_degree
  [Field F]
  {p₁ p₂ : F[X]}
  {d : ℕ}
-- given
  (hd₁ : p₁.natDegree ≤ d)
  (hd₂ : p₂.natDegree ≤ d)
  (_hne : p₁ ≠ p₂) :
-- imply
  Multiset.card (p₁ - p₂).roots ≤ d :=
-- proof
  calc Multiset.card (p₁ - p₂).roots
    ≤ (p₁ - p₂).natDegree := Polynomial.card_roots' _
    _ ≤ max p₁.natDegree p₂.natDegree := Polynomial.natDegree_sub_le p₁ p₂
    _ ≤ d := max_le hd₁ hd₂

end Probabilistic

namespace Probabilistic

/--
[poly_root_count_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma poly_root_count_le
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {p : F[X]}
  {d : ℕ}
-- given
  (hp : p ≠ 0)
  (hd : p.natDegree ≤ d) :
-- imply
  (Finset.univ.filter (fun r : F => Polynomial.IsRoot p r)).card ≤ d := by
-- proof
  calc (Finset.univ.filter (fun r : F => Polynomial.IsRoot p r)).card
    ≤ p.roots.toFinset.card := by
      apply Finset.card_le_card
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hp).mpr hr
    _ ≤ p.roots.card := p.roots.toFinset_card_le
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ d := hd

end Probabilistic

namespace Probabilistic

/--
[poly_root_prob_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma poly_root_prob_le
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {p : F[X]}
  {d : ℕ}
-- given
  (hp : p ≠ 0)
  (hd : p.natDegree ≤ d) :
-- imply
  ((Finset.univ.filter (fun r : F => Polynomial.IsRoot p r)).card : ℚ) / Fintype.card F ≤ (d : ℚ) / Fintype.card F := by
-- proof
  apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr Fintype.card_pos).le
  exact_mod_cast poly_root_count_le p hp d hd

end Probabilistic

namespace Probabilistic

/--
[schwartz_zippel_book](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma schwartz_zippel_book
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {m : ℕ}
  {p : MvPolynomial (Fin m) F}
  {d : ℕ}
-- given
  (hp : p ≠ 0)
  (hd : ∀ i : Fin m, p.degreeOf i ≤ d) :
-- imply
  (#{r ∈ (univ : Finset (Fin m → F)) | MvPolynomial.eval r p = 0} : ℚ≥0) / ((Fintype.card F : ℚ≥0) ^ m) ≤ (d * m : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
-- proof
  rw [show (univ : Finset (Fin m → F)) = piFinset fun _ => (univ : Finset F) from
    piFinset_univ.symm]
  have h := MvPolynomial.schwartz_zippel_sum_degreeOf hp (fun _ => (Finset.univ : Finset F))
  simp only [Finset.card_univ] at h
  calc (#{f ∈ piFinset fun _ => Finset.univ | (MvPolynomial.eval f) p = 0} : ℚ≥0) /
    ((Fintype.card F : ℚ≥0) ^ m)
    = (#{f ∈ piFinset fun _ => Finset.univ | (MvPolynomial.eval f) p = 0} : ℚ≥0) /
      (∏ _ : Fin m, (Fintype.card F : ℚ≥0)) := by simp
    _ ≤ ∑ i : Fin m, ((p.degreeOf i : ℚ≥0) / (Fintype.card F : ℚ≥0)) := h
    _ ≤ ∑ _ : Fin m, ((d : ℚ≥0) / (Fintype.card F : ℚ≥0)) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact Nat.cast_le.mpr (hd i)
    _ = (d * m : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
end Probabilistic
namespace TuringMachine
open TuringMachine


namespace TuringMachine

/--
[decidesWithError_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma decidesWithError_mono
  {Q : Type}
  [DecidableEq Q]
  {Γ : Type}
  [DecidableEq Γ]
  {M : PTM Q Γ}
  {A : Set (List Γ)}
  {ε₁ ε₂ : ℚ}
  {t : ℕ → ℕ}
-- given
  (hle : ε₁ ≤ ε₂)
  (hε₂ : 0 ≤ ε₂)
  (hDec : M.decidesWithError A ε₁ t) :
-- imply
  M.decidesWithError A ε₂ t :=
-- proof
  ⟨hε₂, fun w hw => le_trans (hDec.2.1 w hw) hle,
    fun w hw => le_trans (hDec.2.2 w hw) hle⟩

end TuringMachine

namespace TuringMachine

/--
[error_reduction_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma error_reduction_lt
  {ε : ℚ}
-- given
  (hε_pos : 0 < ε)
  (hε_lt : ε < 1 / 2) :
-- imply
  ε ^ 2 * (3 - 2 * ε) < ε := by
-- proof
  have h1 : ε * (3 - 2 * ε) < 1 := by nlinarith
  nlinarith [sq_nonneg ε]

end TuringMachine

namespace TuringMachine

/--
[error_reduction_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma error_reduction_pos
  {ε : ℚ}
-- given
  (hε_pos : 0 < ε)
  (hε_lt : ε < 1 / 2) :
-- imply
  0 < ε ^ 2 * (3 - 2 * ε) := by
-- proof
  apply mul_pos (sq_pos_of_pos hε_pos)
  linarith

end TuringMachine

namespace TuringMachine

/--
[error_reduction_lt_half](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma error_reduction_lt_half
  {ε : ℚ}
-- given
  (hε_pos : 0 < ε)
  (hε_lt : ε < 1 / 2) :
-- imply
  ε ^ 2 * (3 - 2 * ε) < 1 / 2 :=
-- proof
  lt_trans (error_reduction_lt ε hε_pos hε_lt) hε_lt

end TuringMachine

namespace TuringMachine

/--
[iterError_pos_and_lt_half](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma iterError_pos_and_lt_half
  {ε₁ : ℚ}
-- given
  (hε₁_pos : 0 < ε₁)
  (hε₁_lt : ε₁ < 1 / 2) :
-- imply
  ∀ n, 0 < iterError ε₁ n ∧ iterError ε₁ n < 1 / 2 := by
-- proof
  intro n; induction n with
  | zero => exact ⟨hε₁_pos, hε₁_lt⟩
  | succ n ih =>
    constructor
    · exact error_reduction_pos _ ih.1 ih.2
    · exact error_reduction_lt_half _ ih.1 ih.2

end TuringMachine

namespace TuringMachine

/--
[iterError_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma iterError_pos
  {ε₁ : ℚ}
  {n : ℕ}
-- given
  (hε₁_pos : 0 < ε₁)
  (hε₁_lt : ε₁ < 1 / 2) :
-- imply
  0 < iterError ε₁ n :=
-- proof
  (iterError_pos_and_lt_half ε₁ hε₁_pos hε₁_lt n).1

end TuringMachine

namespace TuringMachine

/--
[iterError_lt_half](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma iterError_lt_half
  {ε₁ : ℚ}
  {n : ℕ}
-- given
  (hε₁_pos : 0 < ε₁)
  (hε₁_lt : ε₁ < 1 / 2) :
-- imply
  iterError ε₁ n < 1 / 2 :=
-- proof
  (iterError_pos_and_lt_half ε₁ hε₁_pos hε₁_lt n).2

end TuringMachine

namespace TuringMachine

/--
[iterError_eventually_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma iterError_eventually_le
  {ε₁ ε₂ : ℚ}
-- given
  (hε₁_pos : 0 < ε₁)
  (hε₁_lt : ε₁ < 1 / 2)
  (hε₂_pos : 0 < ε₂) :
-- imply
  ∃ n, iterError ε₁ n ≤ ε₂ := by
-- proof
  set r := ε₁ * (3 - 2 * ε₁) with hr_def
  have hr_pos : (0 : ℚ) < r := by rw [hr_def]; nlinarith
  have hr_lt : r < 1 := by rw [hr_def]; nlinarith
  have bound : ∀ n, iterError ε₁ n ≤ ε₁ * r ^ n := by
    intro n; induction n with
    | zero => simp [iterError]
    | succ n ih =>
      have hiter_pos := iterError_pos ε₁ hε₁_pos hε₁_lt n
      have hiter_lt := iterError_lt_half ε₁ hε₁_pos hε₁_lt n
      have hiter_le : iterError ε₁ n ≤ ε₁ := by
        clear ih; induction n with
        | zero => simp [iterError]
        | succ m ihm =>
          exact le_trans (le_of_lt (error_reduction_lt _
            (iterError_pos ε₁ hε₁_pos hε₁_lt m)
            (iterError_lt_half ε₁ hε₁_pos hε₁_lt m)))
            (ihm (iterError_pos ε₁ hε₁_pos hε₁_lt m)
              (iterError_lt_half ε₁ hε₁_pos hε₁_lt m))
      have ratio_bound : iterError ε₁ n * (3 - 2 * iterError ε₁ n) ≤ r := by
        rw [hr_def]; nlinarith
      show iterError ε₁ n ^ 2 * (3 - 2 * iterError ε₁ n) ≤ ε₁ * r ^ (n + 1)
      have h1 : iterError ε₁ n ^ 2 * (3 - 2 * iterError ε₁ n) =
        iterError ε₁ n * (iterError ε₁ n * (3 - 2 * iterError ε₁ n)) := by ring
      rw [h1, pow_succ]
      calc iterError ε₁ n * (iterError ε₁ n * (3 - 2 * iterError ε₁ n))
        ≤ iterError ε₁ n * r :=
          mul_le_mul_of_nonneg_left ratio_bound (le_of_lt hiter_pos)
        _ ≤ (ε₁ * r ^ n) * r :=
          mul_le_mul_of_nonneg_right ih (le_of_lt hr_pos)
        _ = ε₁ * (r ^ n * r) := by ring
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε₂_pos hε₁_pos) hr_lt
  refine ⟨n, le_trans (bound n) (le_of_lt ?_)⟩
  rwa [lt_div_iff₀ hε₁_pos, mul_comm] at hn
/-- **Amplification Lemma for BPP (Sipser, Lecture 23).** If `M₁` is a
polynomial-time PTM deciding `A` with error `ε₁ < 1/2`, then for any
`0 < ε₂ < 1/2` there is an equivalent polynomial-time PTM `M₂` deciding `A`
with error `ε₂`. The proof iterates `one_step_majority_vote` until the error
drops below `ε₂`. -/
end TuringMachine
namespace BranchingPrograms
open TuringMachine

end TuringMachine

namespace BranchingPrograms

/--
[eqROBP_numBits_poly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma eqROBP_numBits_poly
-- imply
  IsBigO eqROBP_numBits (fun n => n ^ 2) :=
-- proof
  ⟨2, 1, by norm_num, fun n hn => by simp [eqROBP_numBits]; nlinarith [Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0)]⟩

end BranchingPrograms

namespace BranchingPrograms

/--
[edgeFactor_true](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma edgeFactor_true
  [p₁(r) = p₂(r)]
  {m : ℕ}
  [CommRing R]
  {i : Fin m} :
-- imply
  edgeFactor R i true = MvPolynomial.X i := by
-- proof
  simp [edgeFactor]

end BranchingPrograms

namespace BranchingPrograms

/--
[edgeFactor_false](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma edgeFactor_false
  [p₁(r) = p₂(r)]
  {m : ℕ}
  [CommRing R]
  {i : Fin m} :
-- imply
  edgeFactor R i false = 1 - MvPolynomial.X i := by
-- proof
  simp [edgeFactor]

end BranchingPrograms

namespace BranchingPrograms

/--
[degreeOf_X_le_one'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma degreeOf_X_le_one'
  [p₁(r) = p₂(r)]
  {m : ℕ}
  [CommRing R]
  {i j : Fin m} :
-- imply
  degreeOf j (X i : MvPolynomial (Fin m) R) ≤ 1 := by
-- proof
  rw [degreeOf_le_iff]
  intro d hd
  have : d ∈ ({Finsupp.single i 1} : Finset (Fin m →₀ ℕ)) :=
    support_monomial_subset hd
  rw [Finset.mem_singleton] at this
  subst this
  simp only [Finsupp.single_apply]
  split_ifs <;> omega

end BranchingPrograms

namespace BranchingPrograms

/--
[degreeOf_edgeFactor_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma degreeOf_edgeFactor_le
  [p₁(r) = p₂(r)]
  {m : ℕ}
  [CommRing R]
  {i j : Fin m}
  {b : Bool} :
-- imply
  degreeOf j (edgeFactor R i b) ≤ 1 := by
-- proof
  cases b with
  | true =>
    simp only [edgeFactor_true]
    exact degreeOf_X_le_one' i j
  | false =>
    simp only [edgeFactor_false]
    calc degreeOf j (1 - X i : MvPolynomial (Fin m) R)
      ≤ max (degreeOf j (1 : MvPolynomial (Fin m) R))
        (degreeOf j (X i : MvPolynomial (Fin m) R)) :=
        degreeOf_sub_le j 1 (X i)
      _ ≤ max 0 1 := by
        apply max_le_max
        · exact le_of_eq (degreeOf_one j)
        · exact degreeOf_X_le_one' i j
      _ = 1 := by norm_num

end BranchingPrograms

namespace BranchingPrograms

/--
[degreeOf_X_of_ne'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma degreeOf_X_of_ne'
  [p₁(r) = p₂(r)]
  {m : ℕ}
  [CommRing R]
  {i j : Fin m}
-- given
  (hij : j ≠ i) :
-- imply
  degreeOf j (X i : MvPolynomial (Fin m) R) = 0 := by
-- proof
  apply Nat.le_zero.mp
  rw [degreeOf_le_iff]
  intro d hd
  have : d ∈ ({Finsupp.single i 1} : Finset (Fin m →₀ ℕ)) :=
    support_monomial_subset hd
  rw [Finset.mem_singleton] at this
  subst this
  simp [hij]

end BranchingPrograms

namespace BranchingPrograms

/--
[degreeOf_edgeFactor_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma degreeOf_edgeFactor_of_ne
  [p₁(r) = p₂(r)]
  {m : ℕ}
  [CommRing R]
  {i j : Fin m}
  {b : Bool}
-- given
  (hij : j ≠ i) :
-- imply
  degreeOf j (edgeFactor R i b) = 0 := by
-- proof
  cases b with
  | true =>
    simp only [edgeFactor_true]
    exact degreeOf_X_of_ne' i j hij
  | false =>
    simp only [edgeFactor_false]
    apply Nat.le_zero.mp
    calc degreeOf j (1 - X i : MvPolynomial (Fin m) R)
      ≤ max (degreeOf j (1 : MvPolynomial (Fin m) R))
        (degreeOf j (X i : MvPolynomial (Fin m) R)) :=
        degreeOf_sub_le j 1 (X i)
      _ = max 0 0 := by
        rw [degreeOf_one, degreeOf_X_of_ne' i j hij]
      _ = 0 := by norm_num

end BranchingPrograms

namespace BranchingPrograms

/--
[degreeOf_pathMonomial_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma degreeOf_pathMonomial_le
  [p₁(r) = p₂(r)]
  {m : ℕ}
  [CommRing R]
  {a : Fin m → Bool}
  {j : Fin m} :
-- imply
  degreeOf j (pathMonomial R a) ≤ 1 := by
-- proof
  unfold pathMonomial
  calc degreeOf j (∏ i : Fin m, edgeFactor R i (a i))
    ≤ ∑ i : Fin m, degreeOf j (edgeFactor R i (a i)) :=
      degreeOf_prod_le j Finset.univ _
    _ ≤ ∑ i : Fin m, (if j = i then 1 else 0) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hij
      · subst hij
        exact degreeOf_edgeFactor_le j j (a j)
      · exact le_of_eq (degreeOf_edgeFactor_of_ne i j (a i) hij)
    _ = 1 := by simp

end BranchingPrograms

namespace BranchingPrograms

/--
[arithmetize_degreeOf_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean)
-/
@[path]
lemma arithmetize_degreeOf_le
  [p₁(r) = p₂(r)]
  {m : ℕ}
  [CommRing R]
  {bp : BranchingProgram m}
  {j : Fin m} :
-- imply
  degreeOf j (arithmetize R bp) ≤ 1 := by
-- proof
  unfold arithmetize arithmetizeFn
  calc degreeOf j (∑ a ∈ Finset.univ.filter (fun a => bp.eval a = true), pathMonomial R a)
    ≤ (Finset.univ.filter (fun a => bp.eval a = true)).sup
      (fun a => degreeOf j (pathMonomial R a)) :=
      degreeOf_sum_le j _ _
    _ ≤ 1 := by
      apply Finset.sup_le
      intro a _
      exact degreeOf_pathMonomial_le a j

end BranchingPrograms


-- created on 2026-10-23
