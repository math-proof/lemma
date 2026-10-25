import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.ParabolicPositivity
import Lemma.List.WordSigma.eq.AddSSMul.of.All_Eq_0.Ne
import Lemma.List.EqWordSSigma.of.WordProd
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
open Finset BigOperators CoxeterSystem


namespace CoxeterGroup

/--
[alternatingWord_chain'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralWordPositivity.lean)
-/
@[path]
lemma alternatingWord_chain'
  [DecidableEq B]
  [Fintype B]
  {s t : B}
  {n : ℕ}
-- given
  (hst : s ≠ t) :
-- imply
  List.Chain' (· ≠ ·) (alternatingWord s t n) := by
-- proof
  induction n with
  | zero => exact List.IsChain.nil
  | succ m ih =>
    rw [alternatingWord_succ']
    apply List.IsChain.cons ih
    intro y hy
    match m, ih, hy with
    | 0, _, hy => simp [alternatingWord] at hy
    | k + 1, _, hy =>
      rw [alternatingWord_succ'] at hy
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hy
      by_cases hk : Even k
      · have hk1 : ¬Even (k + 1) := fun h => (Nat.even_add_one.mp h) hk
        simp only [if_pos hk, if_neg hk1]
        exact hst
      · have hk1 : Even (k + 1) := Nat.even_add_one.mpr hk
        simp only [if_neg hk, if_pos hk1]
        exact hst.symm

end CoxeterGroup

namespace CoxeterGroup

/--
[alternatingWord_last_cond](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralWordPositivity.lean)
-/
@[path]
lemma alternatingWord_last_cond
  [DecidableEq B]
  [Fintype B]
  {s t : B}
  {n : ℕ} :
-- imply
  alternatingWord s t n = [] ∨ (∃ h : alternatingWord s t n ≠ [], (alternatingWord s t n).getLast h = t) := by
-- proof
  cases n with
  | zero => left; rfl
  | succ m =>
    right
    have heq : alternatingWord s t (m + 1) = (alternatingWord t s m).concat t :=
      alternatingWord_succ s t m
    have hne : alternatingWord s t (m + 1) ≠ [] := by
      rw [heq]; simp [List.concat_eq_append]
    refine ⟨hne, ?_⟩
    have key : (alternatingWord s t (m + 1)).getLast hne =
      ((alternatingWord t s m) ++ [t]).getLast (by simp) := by
      congr 1
      simp [heq, List.concat_eq_append]
    simp [key]

end CoxeterGroup

namespace CoxeterGroup

/--
[alternatingWord_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralWordPositivity.lean)
-/
@[path]
lemma alternatingWord_pos
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {n : ℕ}
-- given
  (hst : s ≠ t)
  (hlen : n < M s t ∨ M s t = 0) :
-- imply
  IsPositive (wordSigma M (alternatingWord s t n) (e s)) := by
-- proof
  apply parabolic_pos M s t hst (alternatingWord s t n)
  · exact CoxeterSystem.mem_alternatingWord s t n
  · rcases hlen with hlt | hm0
    · left; rwa [length_alternatingWord]
    · right; exact hm0
  · exact alternatingWord_chain' s t hst n
  · exact alternatingWord_last_cond s t n
set_option linter.unusedVariables false in

end CoxeterGroup

namespace CoxeterGroup

/--
[wordSigma_pos_of_word_in_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralWordPositivity.lean)
-/
@[path]
lemma wordSigma_pos_of_word_in_two
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  [Group W]
  {cs : CoxeterSystem M W}
  {s t : B}
  {word : List B}
-- given
  (hst : s ≠ t)
  (hmem : ∀ b ∈ word, b = s ∨ b = t)
  (hlen : cs.length (cs.wordProd word) < M s t ∨ M s t = 0)
  (hform : ∃ n, cs.wordProd word = cs.wordProd (alternatingWord s t n) ∧ (n < M s t ∨ M s t = 0)) :
-- imply
  IsPositive (wordSigma M word (e s)) := by
-- proof
  obtain ⟨n, hprod_eq, hn_bound⟩ := hform
  have h := wordSigma_eq_of_wordProd_eq M cs word (alternatingWord s t n) hprod_eq (e s)
  rw [h]
  exact alternatingWord_pos M s t hst n hn_bound

end CoxeterGroup


-- created on 2026-10-23
