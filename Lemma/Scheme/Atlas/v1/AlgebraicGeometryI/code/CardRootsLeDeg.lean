import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial
open scoped Classical


/--
[card_roots_le_deg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CardRootsLeDeg.lean)
-/
@[path]
lemma card_roots_le_deg
  [CommRing K]
  [IsDomain K]
  {p : K[X]} :
-- imply
  (p.roots.toFinset.card : ℕ) ≤ p.natDegree :=
-- proof
  (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p)


-- created on 2026-10-23
