import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.ProjectiveVariety
open MvPolynomial Set


/--
[mem_projectiveZeroLocus_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ProjectiveVariety.lean)
-/
@[path]
lemma mem_projectiveZeroLocus_iff
  [Field k]
  [Field K]
  [Algebra k K]
  {S : Set (MvPolynomial σ k)}
  {P : Projectivization K (σ → K)} :
-- imply
  P ∈ projectiveZeroLocus k K S ↔ ∀ p ∈ S, aeval P.rep p = 0 :=
-- proof
  Iff.rfl


-- created on 2026-10-23
