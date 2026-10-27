import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.Torus
open StatMech StatMech.Onsager


/--
[onsTorus_card_verts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Torus.lean)
-/
@[path]
private lemma onsTorus_card_verts_eq
  {L : ℕ}
  [NeZero L] :
-- imply
  Fintype.card (ZMod L × ZMod L) = L ^ 2 := by
-- proof
  apply StatMech.Onsager.onsTorus_card_verts L

/--
[onsTorus_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Torus.lean)
-/
@[path]
private lemma onsTorus_degree_eq
  {L : ℕ}
  [Fact (2 < L)]
  {v : ZMod L × ZMod L} :
-- imply
  (onsTorusGraph L).degree v = 4 := by
-- proof
  apply StatMech.Onsager.onsTorus_degree L v

/--
[onsTorus_card_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Torus.lean)
-/
@[path]
private lemma onsTorus_card_edges_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  (onsTorusGraph L).edgeFinset.card = 2 * L ^ 2 := by
-- proof
  apply StatMech.Onsager.onsTorus_card_edges L


-- created on 2026-10-23
