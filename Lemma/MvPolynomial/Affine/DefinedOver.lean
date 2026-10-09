import Mathlib
import sympy.Basic
import sympy.AlgebraicGeometry.Affine.DefinedOver

open MvPolynomial

/--
[mem_idealOverK_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Affine/DefinedOver.lean)
-/
@[path]
private lemma mem_idealOverK_iff_eq
  [Field k]
-- given
  {Z : Set (Fin n → AlgebraicClosure k)} {f : MvPolynomial (Fin n) k} :
-- imply
  f ∈ idealOverK Z ↔
    MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f ∈
      MvPolynomial.vanishingIdeal (AlgebraicClosure k) Z := by
-- proof
  apply MvPolynomial.mem_idealOverK_iff


/--
[isDefinedOver_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Affine/DefinedOver.lean)
-/
@[path]
private lemma isDefinedOver_iff_eq
  [Field k]
-- given
  (Z : Set (Fin n → AlgebraicClosure k)) :
-- imply
  IsDefinedOver Z ↔
    MvPolynomial.vanishingIdeal (AlgebraicClosure k) Z =
      Ideal.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))
        (idealOverK Z) := by
-- proof
  apply MvPolynomial.isDefinedOver_iff


/--
[eval_of_mem_idealOverK](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Affine/DefinedOver.lean)
-/
@[path]
private lemma eval_of_mem_idealOverK_eq
  [Field k]
-- given
  {Z : Set (Fin n → AlgebraicClosure k)} {f : MvPolynomial (Fin n) k}
  (hf : f ∈ idealOverK Z) {P : Fin n → AlgebraicClosure k} (hP : P ∈ Z) :
-- imply
  MvPolynomial.eval P
    (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f) = 0 := by
-- proof
  apply MvPolynomial.eval_of_mem_idealOverK
  · exact hf
  · exact hP


/--
[idealOverK_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Affine/DefinedOver.lean)
-/
@[path]
private lemma idealOverK_empty_eq
  [Field k]
-- given
  (n : ℕ) :
-- imply
  idealOverK (∅ : Set (Fin n → AlgebraicClosure k)) = ⊤ := by
-- proof
  apply MvPolynomial.idealOverK_empty


/--
[idealOverK_anti_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Affine/DefinedOver.lean)
-/
@[path]
private lemma idealOverK_anti_mono_eq
  [Field k]
-- given
  {Z₁ Z₂ : Set (Fin n → AlgebraicClosure k)} (h : Z₁ ⊆ Z₂) :
-- imply
  idealOverK Z₂ ≤ idealOverK Z₁ := by
-- proof
  apply MvPolynomial.idealOverK_anti_mono
  exact h


-- created on 2026-10-09
