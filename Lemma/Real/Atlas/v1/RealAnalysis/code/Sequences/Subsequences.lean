import Mathlib
import sympy.Basic
import Def.v1.Atlas.RealAnalysis.code.Sequences.Subsequences
open Sequences


namespace Sequences

/--
[bolzano_weierstrass](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Sequences/Subsequences.lean)
-/
@[path]
lemma bolzano_weierstrass
  {x : ℕ → ℝ}
-- given
  (hb : Bornology.IsBounded (Set.range x)) :
-- imply
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L, Filter.Tendsto (x ∘ φ) Filter.atTop (nhds L) := by
-- proof
  obtain ⟨a, _, φ, hφ, ha⟩ := tendsto_subseq_of_bounded hb (fun n => Set.mem_range_self n)
  exact ⟨φ, hφ, a, ha⟩

end Sequences

namespace Sequences

/--
[subseq_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Sequences/Subsequences.lean)
-/
@[path]
lemma subseq_tendsto
  {x : ℕ → ℝ}
  {L : ℝ}
  {φ : ℕ → ℕ}
-- given
  (hφ : StrictMono φ)
  (hx : Filter.Tendsto x Filter.atTop (nhds L)) :
-- imply
  Filter.Tendsto (x ∘ φ) Filter.atTop (nhds L) :=
-- proof
  hx.comp hφ.tendsto_atTop

end Sequences


-- created on 2026-10-23
