import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecificLimits.StolzCesaro

open MetaMathlibExt

/--
[StolzCesaro](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Series/StolzCesaro.lean)
-/
@[path]
private lemma stolz_cesaro_is
-- given
  (a b : ℕ → ℝ)
  (hb_mono : StrictMono b)
  (hb_unbounded : Filter.Tendsto b Filter.atTop Filter.atTop)
  (L : ℝ)
  (hlim : Filter.Tendsto (fun n => (a (n + 1) - a n) / (b (n + 1) - b n))
    Filter.atTop (nhds L)) :
-- imply
  Filter.Tendsto (fun n => a n / b n) Filter.atTop (nhds L) := by
-- proof
  apply MetaMathlibExt.stolz_cesaro hb_mono hb_unbounded hlim

-- created on 2026-10-10
