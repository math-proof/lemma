/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/GroupAction/UniformFixedPoints.lean -/


import Lemma.Nat.AddCardMul_SubCard1.eq.MulCard_QuotientOrbitRelCard
import Mathlib.Algebra.Group.Action.TypeTags
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.GroupTheory.GroupAction.UniformFixedPoints

-- Translation by a nonzero element of `ZMod 5` has no fixed points and hence one orbit.
example :
    Nat.card (MulAction.orbitRel.Quotient (Multiplicative (ZMod 5)) (ZMod 5)) = 1 := by
  have h := MulAction.card_add_mul_card_sub_one_eq_card_orbits_mul_card
    (Multiplicative (ZMod 5)) (ZMod 5) 0 (by
      intro g hg
      simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset,
        MulAction.mem_fixedBy, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
        Finset.mem_univ, forall_const]
      intro x hx
      change g.toAdd + x = x at hx
      apply hg
      apply Multiplicative.ext
      simpa using hx)
  norm_num [Nat.card_eq_fintype_card] at h
  omega

end MathlibExtTest.GroupTheory.GroupAction.UniformFixedPoints
