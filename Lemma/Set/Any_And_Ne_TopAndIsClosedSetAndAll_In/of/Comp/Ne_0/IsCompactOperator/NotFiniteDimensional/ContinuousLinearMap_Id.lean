import Mathlib
import sympy.Basic
import Theorem.Analysis.NormedSpace.LomonosovInvariantSubspace.Part2

/--
[LomonosovInvariantSubspace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/LomonosovInvariantSubspace.lean)
-/
@[path]
private lemma lomonosov_invariant_subspace_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (K T : ContinuousLinearMap (RingHom.id ℂ) E E)
  (hInf : ¬ FiniteDimensional ℂ E)
  (hK_compact : IsCompactOperator K)
  (hK_ne : K ≠ 0)
  (hComm : T.comp K = K.comp T) :
-- imply
  ∃ M : Submodule ℂ E, M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set E) ∧ ∀ x ∈ M, T x ∈ M := by
-- proof
  apply FunctionalAnalysis.LomonosovInvariantSubspaceWanted.lomonosov_invariantSubspace
    hInf K hK_compact hK_ne T hComm

-- created on 2026-10-10
