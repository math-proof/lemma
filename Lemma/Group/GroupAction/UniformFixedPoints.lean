import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.GroupAction.UniformFixedPoints
open MetaMathlibExt


/--
[_root_.MulAction.card_add_mul_card_sub_one_eq_card_orbits_mul_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GroupAction/UniformFixedPoints.lean)
-/
@[path]
private lemma _root__MulAction_card_add_mul_card_sub_one_eq_card_orbits_mul_card_eq
  [Group G] [MulAction G X] [Finite G] [Finite X]
  {c : ℕ}
-- given
  (hfixed : ∀ g : G, g ≠ 1 → Nat.card (MulAction.fixedBy X g) = c) :
-- imply
  Nat.card X + c * (Nat.card G - 1) =
      Nat.card (MulAction.orbitRel.Quotient G X) * Nat.card G := by
-- proof
  apply MetaMathlibExt._root_.MulAction.card_add_mul_card_sub_one_eq_card_orbits_mul_card G X c hfixed


-- created on 2026-10-20
