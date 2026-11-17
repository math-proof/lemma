module

public import Mathlib
public import Def.v1.Atlas.EllipticCurves.code.ProjectiveVariety

public section

open MvPolynomial Set


/--
[mem_projectiveZeroLocus_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ProjectiveVariety.lean)
-/
public theorem mem_projectiveZeroLocus_iff
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
