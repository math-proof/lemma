import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
open MetaMathlibExt


/--
[multigradedPoincareCoefficients_hasFiniteSupport_of_finiteResolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean)
-/
@[path]
private lemma multigradedPoincareCoefficients_hasFiniteSupport_of_finiteResolution_eq
  {K : Type u} [Field K]
  {n : ℕ}
  {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M]
  {targetGraded : MultigradedPolynomialModule K n M}
  {resolution : CategoryTheory.ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M)}
  {ι : ℕ → Type u}
  {res : MultigradedFreeResolution K n M targetGraded resolution ι}
  {data : MultigradedBaseChange targetGraded resolution ι res}
  {bound : ℕ}
-- given
  (finiteBasis : ∀ i, Finite (ι i))
  (emptyAbove : ∀ i, bound < i → IsEmpty (ι i)) :
-- imply
  Function.HasFiniteSupport (multigradedPoincareCoefficients data) := by
-- proof
  apply MetaMathlibExt.multigradedPoincareCoefficients_hasFiniteSupport_of_finiteResolution data bound finiteBasis emptyAbove


-- created on 2026-10-20
