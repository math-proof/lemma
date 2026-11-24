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
public import Def.Algebra.Lie.WittMultigradedDimension.Part9
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

attribute [local instance 100] LieRing.ofAssociativeRing

theorem wittLyndonPairEncode_injective {r n : ℕ} :
    Function.Injective (wittLyndonPairEncode : WittLyndonPair r n →
      List.Vector (Fin r) n × Fin (n + 1)) := by
  intro p q hpq
  have hconcat : p.1.1 ++ p.1.2 = q.1.1 ++ q.1.2 :=
    congr_arg (fun z : List.Vector (Fin r) n × Fin (n + 1) => z.1.1) hpq
  have hlen : p.1.1.length = q.1.1.length :=
    congr_arg (fun z : List.Vector (Fin r) n × Fin (n + 1) => z.2.1) hpq
  apply Subtype.ext
  apply Prod.ext
  · calc
      p.1.1 = (p.1.1 ++ p.1.2).take p.1.1.length := by simp
      _ = (q.1.1 ++ q.1.2).take p.1.1.length := congr_arg _ hconcat
      _ = q.1.1 := by rw [hlen]; simp
  · calc
      p.1.2 = (p.1.1 ++ p.1.2).drop p.1.1.length := by simp
      _ = (q.1.1 ++ q.1.2).drop p.1.1.length := congr_arg _ hconcat
      _ = q.1.2 := by rw [hlen]; simp

end MetaMathlibExt
