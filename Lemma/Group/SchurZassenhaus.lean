import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.SchurZassenhaus
open scoped Pointwise
open MulAction MulOpposite Subgroup QuotientGroup Function
open MathlibExt.GroupTheory.SchurZassenhausWanted


/--
[schur_zassenhaus_conjugate_complements](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma schur_zassenhaus_conjugate_complements_eq
  [Group G] [Finite G]
  {N : Subgroup G} [N.Normal] [Group.IsSolvable N]
  {K₁ K₂ : Subgroup G}
-- given
  (hN : Nat.Coprime (Nat.card N) N.index)
  (h₁ : N.IsComplement' K₁)
  (h₂ : N.IsComplement' K₂) :
-- imply
  ∃ g : G, g ∈ N ∧ K₁.map (MulAut.conj g).toMonoidHom = K₂ := by
-- proof
  apply MathlibExt.GroupTheory.SchurZassenhausWanted.schur_zassenhaus_conjugate_complements N hN K₁ K₂ h₁ h₂


-- created on 2026-10-20
