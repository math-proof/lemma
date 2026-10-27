import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.RealAnalysis.code.Series.Basic
open Real_Analysis Real_Analysis.Series
open Filter Finset


namespace Real_Analysis.Series

/--
[abs_convergent_rearrangement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Series/Basic.lean)
-/
@[path]
lemma abs_convergent_rearrangement
  {x : ℕ → ℝ}
  {σ : ℕ ≃ ℕ}
-- given
  (habs : Summable (fun n => |x n|))
  (hsum : HasSum x s) :
-- imply
  Summable (fun n => |x (σ n)|) ∧ HasSum (x ∘ σ) s := by
-- proof
  exact ⟨(Equiv.summable_iff σ).mpr habs, (Equiv.hasSum_iff σ).mpr hsum⟩
open Filter Finset

end Real_Analysis.Series


-- created on 2026-10-23
