/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.HNNExtension
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# Higman–Neumann–Neumann embedding theorem

Records that every countable group embeds into a two-generator group.
-/


section

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

universe u

open SemidirectProduct

noncomputable def shiftAut : MulAut (FreeGroup ℤ) :=
  FreeGroup.freeGroupCongr (Equiv.addRight (1 : ℤ))

noncomputable def shiftHom : Multiplicative ℤ →* MulAut (FreeGroup ℤ) :=
  (zpowersHom (MulAut (FreeGroup ℤ))) shiftAut

end MathlibExt.GroupTheory.HNNEmbeddingWanted
end
