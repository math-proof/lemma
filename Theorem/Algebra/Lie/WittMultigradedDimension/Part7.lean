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
import Def.Algebra.Lie.WittMultigradedDimension.Part6
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

theorem wittTriangular_mul (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} {x y : FreeAlgebra K (Fin r)}
    (hx : WittTriangular K u x) (hy : WittTriangular K v y) :
    x * y - wittAssocWord K (u ++ v) ∈ wittWordSpanGT K (u ++ v) := by
  rw [← wittAssocWord_mul]
  have hxy : x * y - wittAssocWord K u * wittAssocWord K v =
      (x - wittAssocWord K u) * y + wittAssocWord K u * (y - wittAssocWord K v) := by
    rw [sub_mul, mul_sub]
    abel
  rw [hxy]
  apply Submodule.add_mem
  · exact wittWordSpanGT_mul_spanGE K hx (wittTriangular_mem_spanGE K hy)
  · exact wittWordSpanGE_mul_spanGT K (wittAssocWord_mem_spanGE K u) hy

theorem wittTriangular_reverse_mul (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} {x y : FreeAlgebra K (Fin r)}
    (hx : WittTriangular K u x) (hy : WittTriangular K v y)
    (hlt : u ++ v < v ++ u) : y * x ∈ wittWordSpanGT K (u ++ v) := by
  have hcontent : wittWordContent (v ++ u) = wittWordContent (u ++ v) := by
    rw [wittWordContent_append, wittWordContent_append]
    funext i
    exact Nat.add_comm _ _
  exact (wittWordSpanGE_le_spanGT_of_lt K hcontent hlt)
    (wittWordSpanGE_mul_spanGE K
      (wittTriangular_mem_spanGE K hy) (wittTriangular_mem_spanGE K hx))

theorem wittLyndon_append_lt_swap {α : Type*} [LinearOrder α]
    {u v : List α} (hu : IsLyndonWord u) (hv : IsLyndonWord v) (huv : u < v) :
    u ++ v < v ++ u := by
  have huvL : WittSuffixLyndon (u ++ v) :=
    wittSuffixLyndon_append ((wittLyndon_iff_suffix u).mp hu)
      ((wittLyndon_iff_suffix v).mp hv) huv
  exact (huvL.2 u v hu.1 hv.1 rfl).trans_le (wittLe_append_self v u)

end MetaMathlibExt
