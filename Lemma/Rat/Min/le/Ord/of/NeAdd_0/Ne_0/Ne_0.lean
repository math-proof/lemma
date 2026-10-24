import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup


namespace Definitions
end Definitions
open Definitions
open AlgebraicCurve


private lemma le_ord_add
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
  min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hfg' := v.adicValuation_ne_zero hfg
  have hmax : v.adicValuation (f + g) ≤ max (v.adicValuation f) (v.adicValuation g) := Valuation.map_add _ _ _
  unfold Place.ord
  refine Or.elim (le_max_iff.mp hmax) ?_ ?_
  ·
    intro hle
    have := (WithZero.log_le_log hfg' hf').mpr hle
    omega
  ·
    intro hle
    have := (WithZero.log_le_log hfg' hg').mpr hle
    omega
/--
[AlgebraicCurve_Place_min_ord_le_ord_add](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_min_ord_le_ord_add.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {v : AlgebraicCurve.Place K F}
  {f g : F}
-- given
  (hf : f ≠ 0)
  (hg : g ≠ 0)
  (hfg : f + g ≠ 0) :
-- imply
  min (v.ord f) (v.ord g) ≤ v.ord (f + g) :=
-- proof
  le_ord_add v hf hg hfg


-- created on 2026-10-24
