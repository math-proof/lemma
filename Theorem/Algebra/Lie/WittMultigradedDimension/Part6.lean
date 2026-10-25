/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Dimension.Finite
import Def.Algebra.Lie.FreeLieMultihomogeneousComponent
import Def.Algebra.Lie.WittMultigradedValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Rotate
import Theorem.Combinatorics.Words.LyndonWord.Part14
import Lemma.Finset.Words.LyndonWord
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeAlgebra
import Def.Algebra.Lie.WittMultigradedDimension.Part5
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

theorem wittAppend_le_append_of_le_of_le {α : Type*} [LinearOrder α]
    {u u' v v' : List α} (hu : u ≤ u') (hlen : u.length = u'.length)
    (hv : v ≤ v') : u ++ v ≤ u' ++ v' := by
  rcases hu.eq_or_lt with rfl | hu
  · rcases hv.eq_or_lt with rfl | hv
    · exact le_rfl
    · exact ((wittAppend_left_lt_iff u v v').mpr hv).le
  · apply (wittAppend_right_lt_of_length_eq hu hlen v).le.trans
    rcases hv.eq_or_lt with rfl | hv
    · exact le_rfl
    · exact ((wittAppend_left_lt_iff u' v v').mpr hv).le

theorem wittAppend_lt_append_of_lt_of_le {α : Type*} [LinearOrder α]
    {u u' v v' : List α} (hu : u < u') (hlen : u.length = u'.length)
    (hv : v ≤ v') : u ++ v < u' ++ v' :=
  (wittAppend_right_lt_of_length_eq hu hlen v).trans_le (by
    rcases hv.eq_or_lt with rfl | hv
    · exact le_rfl
    · exact ((wittAppend_left_lt_iff u' v v').mpr hv).le)

theorem wittAppend_lt_append_of_le_of_lt {α : Type*} [LinearOrder α]
    {u u' v v' : List α} (hu : u ≤ u') (hlen : u.length = u'.length)
    (hv : v < v') : u ++ v < u' ++ v' := by
  rcases hu.eq_or_lt with rfl | hu
  · exact (wittAppend_left_lt_iff u v v').mpr hv
  · exact (wittAppend_right_lt_of_length_eq hu hlen v).trans
      ((wittAppend_left_lt_iff u' v v').mpr hv)

theorem wittWordSpanGE_mul_spanGE (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} {x y : FreeAlgebra K (Fin r)}
    (hx : x ∈ wittWordSpanGE K u) (hy : y ∈ wittWordSpanGE K v) :
    x * y ∈ wittWordSpanGE K (u ++ v) := by
  apply witt_mul_mem_wordSpan K (S := WittWordsGE u) (T := WittWordsGE v)
  · intro u' hu' v' hv'
    refine ⟨?_, ?_⟩
    · rw [wittWordContent_append, wittWordContent_append, hu'.1, hv'.1]
    · exact wittAppend_le_append_of_le_of_le hu'.2
        (wittWordContent_eq_length_eq hu'.1.symm) hv'.2
  · exact hx
  · exact hy

theorem wittWordSpanGT_mul_spanGE (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} {x y : FreeAlgebra K (Fin r)}
    (hx : x ∈ wittWordSpanGT K u) (hy : y ∈ wittWordSpanGE K v) :
    x * y ∈ wittWordSpanGT K (u ++ v) := by
  apply witt_mul_mem_wordSpan K (S := WittWordsGT u) (T := WittWordsGE v)
  · intro u' hu' v' hv'
    refine ⟨?_, ?_⟩
    · rw [wittWordContent_append, wittWordContent_append, hu'.1, hv'.1]
    · exact wittAppend_lt_append_of_lt_of_le hu'.2
        (wittWordContent_eq_length_eq hu'.1.symm) hv'.2
  · exact hx
  · exact hy

theorem wittWordSpanGE_mul_spanGT (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} {x y : FreeAlgebra K (Fin r)}
    (hx : x ∈ wittWordSpanGE K u) (hy : y ∈ wittWordSpanGT K v) :
    x * y ∈ wittWordSpanGT K (u ++ v) := by
  apply witt_mul_mem_wordSpan K (S := WittWordsGE u) (T := WittWordsGT v)
  · intro u' hu' v' hv'
    refine ⟨?_, ?_⟩
    · rw [wittWordContent_append, wittWordContent_append, hu'.1, hv'.1]
    · exact wittAppend_lt_append_of_le_of_lt hu'.2
        (wittWordContent_eq_length_eq hu'.1.symm) hv'.2
  · exact hx
  · exact hy

end MetaMathlibExt
