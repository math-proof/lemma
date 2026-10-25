/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/Arrow.lean -/

import Mathlib.Data.Fintype.Basic
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.SuccPred
import Def.GameTheory.SocialChoice.Arrow


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
