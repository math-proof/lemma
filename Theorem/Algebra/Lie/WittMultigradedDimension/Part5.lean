module
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Def.Algebra.Lie.FreeLieMultihomogeneousComponent
public import Def.Algebra.Lie.WittMultigradedValue
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.Rotate
public import Theorem.Combinatorics.Words.LyndonWord.Part14
public import Theorem.Finset.Words.LyndonWord
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeAlgebra
public import Def.Algebra.Lie.WittMultigradedDimension.Part4
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/
namespace MetaMathlibExt

theorem wittLyndonBracket_isMonomial (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) (hw : IsLyndonWord w) :
    IsFreeLieMonomial K (wittWordContent w) (wittLyndonBracket K w hw) := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      rw [wittLyndonBracket]
      split_ifs with hlen
      · obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hlen
        convert IsFreeLieMonomial.gen (K := K) i using 1
        · ext j
          by_cases hji : j = i
          · subst j
            simp [wittWordContent]
          · simp [wittWordContent, hji, Ne.symm hji]
        · simp
      · have hw2 : 2 ≤ w.length := by
          have hw0 := List.length_pos_of_ne_nil hw.1
          omega
        let u := wittLongestLyndonPrefix w hw2
        let v := wittLongestLyndonSuffix w hw2
        have hfac := wittStandardFactorization hw hw2
        have hu_len : u.length < n := by
          rw [← hn, length_wittLongestLyndonPrefix]
          exact (wittLongestLyndonSuffixIndex_spec w hw2).2.1
        have hv_len : v.length < n := by
          change (wittLongestLyndonSuffix w hw2).length < n
          rw [← hn, wittLongestLyndonSuffix, List.length_drop]
          have hk := (wittLongestLyndonSuffixIndex_spec w hw2).1
          omega
        have hu := ih u.length hu_len u hfac.1 rfl
        have hv := ih v.length hv_len v hfac.2.1 rfl
        have huv : wittWordContent w = fun i => wittWordContent u i + wittWordContent v i := by
          rw [wittLongestLyndon_append w hw2, wittWordContent_append]
        rw [huv]
        exact IsFreeLieMonomial.bracket hu hv

end MetaMathlibExt
