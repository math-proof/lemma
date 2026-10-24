import Mathlib
import sympy.Basic

/--
[closed_graph_theorem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/ClosedGraph.lean)
-/
@[path]
lemma closed_graph_theorem_iff
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V]
  [NormedSpace 𝕜 V]
  [CompleteSpace V]
  [NormedAddCommGroup W]
  [NormedSpace 𝕜 W]
  [CompleteSpace W]
  {T : V →ₗ[𝕜] W} :
-- imply
  Continuous T ↔ IsClosed (T.graph : Set (V × W)) := by
-- proof
  constructor
  · intro hT
    have : (T.graph : Set (V × W)) = {p : V × W | p.2 = T p.1} := by
      ext ⟨x, y⟩; simp [LinearMap.mem_graph_iff]
    rw [this]
    exact isClosed_eq continuous_snd (hT.comp continuous_fst)
  · exact T.continuous_of_isClosed_graph


-- created on 2026-10-23
-- updated on 2026-10-24
