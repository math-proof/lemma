import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.DivisorClassGroup


namespace Definitions
end Definitions
open Definitions
open AlgebraicCurve


/-- ported from external source -/

private lemma  ord_add_eq_of_lt
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
  (h : v.ord f < v.ord g) : v.ord (f + g) = v.ord f := by
  have hval : v.adicValuation g < v.adicValuation f := by
    have hf' := v.adicValuation_ne_zero hf
    have hg' := v.adicValuation_ne_zero hg
    rw [← WithZero.log_lt_log hg' hf']
    unfold Place.ord at h
    omega
  unfold Place.ord
  rw [Valuation.map_add_eq_of_lt_left _ hval]
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {v : AlgebraicCurve.Place K F}
  {f g : F}
-- given
  (hf : f ≠ 0)
  (hg : g ≠ 0)
  (h : v.ord f < v.ord g) :
-- imply
  v.ord (f + g) = v.ord f :=
-- proof
  ord_add_eq_of_lt v hf hg h


-- created on 2026-10-24
