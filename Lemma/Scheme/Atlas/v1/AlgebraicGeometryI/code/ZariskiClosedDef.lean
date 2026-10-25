import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ZariskiClosedDef
open MvPolynomial


/--
[mem_affineZeroLocus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ZariskiClosedDef.lean)
-/
@[path]
lemma mem_affineZeroLocus
  {n : ℕ}
  [CommRing k]
  {S : Set (MvPolynomial (Fin n) k)}
  {p : Fin n → k} :
-- imply
  p ∈ AffineZeroLocus k S ↔ ∀ f ∈ S, MvPolynomial.aeval p f = 0 :=
-- proof
  Iff.rfl

/--
[affineZeroLocus_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ZariskiClosedDef.lean)
-/
@[path]
lemma affineZeroLocus_mono
  {n : ℕ}
  [CommRing k]
  {S T : Set (MvPolynomial (Fin n) k)}
-- given
  (h : S ⊆ T) :
-- imply
  AffineZeroLocus k T ⊆ AffineZeroLocus k S := by
-- proof
  intro p hp f hf
  exact hp f (h hf)


-- created on 2026-10-23
