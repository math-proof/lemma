import Mathlib
import sympy.Basic
import sympy.calculus.functional_analysis.LocalReflexivity

/--
[LocalReflexivity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/LocalReflexivity.lean)
-/
@[path]
private lemma principle_of_local_reflexivity_eq
-- given
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N] [FiniteDimensional 𝕜 N]
  (iM : M →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
  (iN : N →L[𝕜] StrongDual 𝕜 E)
  (ε : ℝ)
  (hM_inj : Function.Injective iM)
  (hN_inj : Function.Injective iN)
  (hε : 0 < ε) :
-- imply
  ∃ T : M →L[𝕜] E,
    (∀ m : M, (1 + ε)⁻¹ * ‖iM m‖ ≤ ‖T m‖ ∧ ‖T m‖ ≤ (1 + ε) * ‖iM m‖)
    ∧ (∀ (m : M) (n : N), (iN n) (T m) = (iM m) (iN n))
    ∧ (∀ (m : M) (x : E), iM m = NormedSpace.inclusionInDoubleDual 𝕜 E x → T m = x) := by
-- proof
  apply FunctionalAnalysis.LocalReflexivityWanted.principle_of_local_reflexivity iM iN hM_inj hN_inj ε hε

-- created on 2026-10-10
