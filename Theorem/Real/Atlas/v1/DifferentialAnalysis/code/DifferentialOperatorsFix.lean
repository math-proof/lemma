module

public import Mathlib
public import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperatorsFix

public section

open MeasureTheory Distribution Set
open scoped SchwartzMap Topology


namespace Distribution

/--
[singSupp_compl_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperatorsFix.lean)
-/
public theorem singSupp_compl_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [MeasureSpace E]
  [BorelSpace E]
  {u : 𝓢'(E, ℂ)} :
-- imply
  (singSupp u)ᶜ = ⋃₀ {s : Set E | IsOpen s ∧ IsSmoothOn' u s} := by
-- proof
  simp [singSupp]

end Distribution

namespace Distribution

/--
[notMem_singSupp_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperatorsFix.lean)
-/
public theorem notMem_singSupp_iff
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [MeasureSpace E]
  [BorelSpace E]
  {u : 𝓢'(E, ℂ)}
  {x : E} :
-- imply
  x ∉ singSupp u ↔ ∃ s : Set E, IsOpen s ∧ IsSmoothOn' u s ∧ x ∈ s := by
-- proof
  simp [← mem_compl_iff, singSupp_compl_eq, mem_sUnion, and_assoc]
end Distribution



-- created on 2026-10-23
-- updated on 2026-11-15
