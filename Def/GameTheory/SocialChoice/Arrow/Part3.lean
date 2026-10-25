/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/Arrow.lean -/

import Mathlib.Data.Fintype.Basic
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.SuccPred
import Theorem.GameTheory.SocialChoice.Arrow.Part2


section

namespace MathlibExt.GameTheory.SocialChoice.ArrowWanted

/-- Strict total order ranking `x` above `y` above `z` above everything else. -/
noncomputable def mkOrder3 {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (x y z : Alt) (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) : StrictTotalOrder Alt where
  lt := fun u v => rank3 (Alt := Alt) x y z u < rank3 (Alt := Alt) x y z v
  irrefl := fun a h => (lt_irrefl _) h
  trans := fun h1 h2 => Nat.lt_trans h1 h2
  total := by
    intro a b hab
    have hne : rank3 (Alt := Alt) x y z a ≠ rank3 (Alt := Alt) x y z b :=
      fun he => hab (rank3_injective x y z h1 h2 h3 he)
    exact lt_or_gt_of_ne hne

/-- `C` is decisive for the ordered pair `(a, b)`: whenever every member of `C`
ranks `a` above `b`, so does society. -/
def decFor {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter)
    (C : Finset Voter) (a b : Alt) : Prop :=
  ∀ p : Profile Alt Voter, (∀ i ∈ C, (p i).lt a b) → (F p).lt a b

end MathlibExt.GameTheory.SocialChoice.ArrowWanted
end
