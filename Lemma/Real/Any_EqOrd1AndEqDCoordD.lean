import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Scheme.CanonicalDivisor
open KaehlerDifferential AlgebraicCurve


/--
Every place admits a uniformizer with ord = 1 and dCoord = D.
-/
@[path]
private lemma main
  [Field K]
  [Field F]
  [Algebra K F]
  {v : Place K F} :
-- imply
  ∃ π : F, v.ord π = 1 ∧ v.dCoord = D K F π := by
-- proof
  refine ⟨((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F), ?_, rfl⟩
  exact v.ord_coe_irreducible
    (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec


-- created on 2026-10-24
