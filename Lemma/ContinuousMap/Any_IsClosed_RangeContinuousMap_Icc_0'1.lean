import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.NormedSpace.Geometric.Part9

/--
[Geometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/Geometric.lean)
-/
@[path]
private lemma banach_mazur_embedding_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E] :
-- imply
  ∃ (e : LinearIsometry (RingHom.id ℝ) E (ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ)),
    IsClosed (Set.range (e : E → ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ)) := by
-- proof
  apply FunctionalAnalysis.GeometricWanted.banachMazur_embedding

-- created on 2026-10-10
