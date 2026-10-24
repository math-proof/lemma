import Mathlib
import sympy.Basic
open KaehlerDifferential Algebra


/--
[smooth_subvariety_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothSubvarietyChar.lean)
-/
@[path]
lemma smooth_subvariety_char
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  [FormallySmooth k R]
  {I : Ideal R} :
-- imply
  FormallySmooth k (R ⧸ I) ↔ ∃ l, l ∘ₗ (kerCotangentToTensor k R (R ⧸ I)) = LinearMap.id :=
-- proof
  FormallySmooth.iff_split_injection Ideal.Quotient.mk_surjective


-- created on 2026-10-23
