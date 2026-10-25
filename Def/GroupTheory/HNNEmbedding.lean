/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Basic.Countable.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.HNNExtension
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
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
