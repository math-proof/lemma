/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/Arrow.lean -/
module

public import Mathlib.Data.Fintype.Basic
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.SuccPred
public import Def.GameTheory.SocialChoice.Arrow

public section

section

namespace MathlibExt.GameTheory.SocialChoice.ArrowWanted

lemma baseRank_injective {Alt : Type*} [Fintype Alt] :
    Function.Injective (baseRank (Alt := Alt)) := by
  intro a b h
  unfold baseRank at h
  have h2 : Fintype.equivFin Alt a = Fintype.equivFin Alt b := Fin.val_injective h
  exact (Fintype.equivFin Alt).injective h2

end MathlibExt.GameTheory.SocialChoice.ArrowWanted
end
