import Mathlib
import sympy.Basic
import sympy.calculus.functional_analysis.EberleinSmulian

/--
[EberleinSmulian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/EberleinSmulian.lean)
-/
@[path]
private lemma eberlein_smulian_iff
-- given
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {s : Set (WeakSpace 𝕜 E)} :
-- imply
  IsCompact s ↔ IsSeqCompact s := by
-- proof
  apply FunctionalAnalysis.BanachSpaceWanted.eberlein_smulian

-- created on 2026-10-10
