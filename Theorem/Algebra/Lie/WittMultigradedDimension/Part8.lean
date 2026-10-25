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
import Def.Algebra.Lie.WittMultigradedDimension.Part7
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

attribute [local instance 100] LieRing.ofAssociativeRing

theorem wittAssocLift_lyndonBracket_triangular (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) (hw : IsLyndonWord w) :
    WittTriangular K w (wittAssocLift K (wittLyndonBracket K w hw)) := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      rw [wittLyndonBracket]
      split_ifs with hlen
      · obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hlen
        unfold WittTriangular
        rw [wittAssocLift, FreeLieAlgebra.lift_of_apply]
        simp only [List.head_cons]
        rw [← wittAssocWord_singleton]
        simp
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
        have hswap : u ++ v < v ++ u :=
          wittLyndon_append_lt_swap hfac.1 hfac.2.1 hfac.2.2
        have hmul := wittTriangular_mul K hu hv
        have hrev := wittTriangular_reverse_mul K hu hv hswap
        unfold WittTriangular
        rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
        have heq :
            (wittAssocLift K (wittLyndonBracket K u hfac.1) *
                wittAssocLift K (wittLyndonBracket K v hfac.2.1) -
              wittAssocLift K (wittLyndonBracket K v hfac.2.1) *
                wittAssocLift K (wittLyndonBracket K u hfac.1)) -
                wittAssocWord K (u ++ v) =
              (wittAssocLift K (wittLyndonBracket K u hfac.1) *
                  wittAssocLift K (wittLyndonBracket K v hfac.2.1) -
                wittAssocWord K (u ++ v)) -
              wittAssocLift K (wittLyndonBracket K v hfac.2.1) *
                wittAssocLift K (wittLyndonBracket K u hfac.1) := by
          abel
        have hfinal :
            (wittAssocLift K (wittLyndonBracket K u hfac.1) *
                wittAssocLift K (wittLyndonBracket K v hfac.2.1) -
              wittAssocLift K (wittLyndonBracket K v hfac.2.1) *
                wittAssocLift K (wittLyndonBracket K u hfac.1)) -
                wittAssocWord K (u ++ v) ∈ wittWordSpanGT K (u ++ v) := by
          rw [heq]
          exact Submodule.sub_mem _ hmul hrev
        have hwuv : w = u ++ v := wittLongestLyndon_append w hw2
        rw [← hwuv] at hfinal
        exact hfinal

end MetaMathlibExt
