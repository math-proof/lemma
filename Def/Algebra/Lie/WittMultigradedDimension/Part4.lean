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
import Theorem.Algebra.Lie.WittMultigradedDimension.Part4
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

noncomputable def wittLyndonBracket (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) (hw : IsLyndonWord w) : FreeLieAlgebra K (Fin r) :=
  if hlen : w.length = 1 then
    FreeLieAlgebra.of K (w.head hw.1)
  else
    let hw2 : 2 ≤ w.length := by
      have hw0 := List.length_pos_of_ne_nil hw.1
      omega
    let hfac := wittStandardFactorization hw hw2
    ⁅wittLyndonBracket K (wittLongestLyndonPrefix w hw2) hfac.1,
      wittLyndonBracket K (wittLongestLyndonSuffix w hw2) hfac.2.1⁆
termination_by w.length
decreasing_by
  · rw [length_wittLongestLyndonPrefix]
    exact (wittLongestLyndonSuffixIndex_spec w hw2).2.1
  · rw [wittLongestLyndonSuffix, List.length_drop]
    have hk := (wittLongestLyndonSuffixIndex_spec w hw2).1
    omega

end MetaMathlibExt
