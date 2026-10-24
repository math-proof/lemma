import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.GenusZeroP1
open AlgebraicGeometry CategoryTheory Polynomial


/--
[projectiveLineAsCurve_genus_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusZeroP1.lean)
-/
@[path]
lemma projectiveLineAsCurve_genus_zero
  {k : Type*}
  [Field k] :
-- imply
  (projectiveLineAsCurve k).genus = 0 := by
-- proof
  rfl

/--
[projectiveLineAsCurve_hasRationalPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusZeroP1.lean)
-/
@[path]
lemma projectiveLineAsCurve_hasRationalPoint
  {k : Type*}
  [Field k] :
-- imply
  (projectiveLineAsCurve k).HasRationalPoint := by
-- proof
  refine ⟨Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (RingHom.id k) (0 : k))), ?_⟩
  show Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (RingHom.id k) (0 : k))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_id]
  congr 1
  ext x
  simp [Polynomial.eval₂_C]

/--
[SmoothProjectiveCurveOverField.genus_eq_of_k_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusZeroP1.lean)
-/
@[path]
lemma SmoothProjectiveCurveOverField.genus_eq_of_k_iso
  [Field k]
  {C₁ C₂ : SmoothProjectiveCurveOverField k}
  {φ : C₁.toScheme ≅ C₂.toScheme}
-- given
  (hφ : φ.hom ≫ C₂.structureMorphism = C₁.structureMorphism) :
-- imply
  C₁.genus = C₂.genus :=
-- proof
  genus_eq_of_scheme_iso C₁ C₂ φ hφ

/--
[SmoothProjectiveCurveOverField.hasRationalPoint_of_k_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusZeroP1.lean)
-/
@[path]
lemma SmoothProjectiveCurveOverField.hasRationalPoint_of_k_iso
  [Field k]
  {C₁ C₂ : SmoothProjectiveCurveOverField k}
  {φ : C₁.toScheme ≅ C₂.toScheme}
-- given
  (hφ : φ.hom ≫ C₂.structureMorphism = C₁.structureMorphism)
  (hpt : C₂.HasRationalPoint) :
-- imply
  C₁.HasRationalPoint := by
-- proof
  obtain ⟨s, hs⟩ := hpt
  refine ⟨s ≫ φ.inv, ?_⟩
  rw [← hφ]
  simp [Iso.inv_hom_id_assoc, hs]

/--
[SmoothProjectiveCurveOverField.genus_zero_of_isIsomorphicToP1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusZeroP1.lean)
-/
@[path]
lemma SmoothProjectiveCurveOverField.genus_zero_of_isIsomorphicToP1
  [Field k]
  {C : SmoothProjectiveCurveOverField k}
-- given
  (hiso : C.IsIsomorphicToP1) :
-- imply
  C.genus = 0 := by
-- proof
  obtain ⟨φ, hφ⟩ := hiso
  have h := SmoothProjectiveCurveOverField.genus_eq_of_k_iso C (projectiveLineAsCurve k) φ hφ
  rw [h, projectiveLineAsCurve_genus_zero]

/--
[SmoothProjectiveCurveOverField.hasRationalPoint_of_isIsomorphicToP1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusZeroP1.lean)
-/
@[path]
lemma SmoothProjectiveCurveOverField.hasRationalPoint_of_isIsomorphicToP1
  [Field k]
  {C : SmoothProjectiveCurveOverField k}
-- given
  (hiso : C.IsIsomorphicToP1) :
-- imply
  C.HasRationalPoint := by
-- proof
  obtain ⟨φ, hφ⟩ := hiso
  exact C.hasRationalPoint_of_k_iso (projectiveLineAsCurve k) φ hφ
    (projectiveLineAsCurve_hasRationalPoint k)
/-- Theorem 23.1 (forward direction): a smooth projective curve of genus zero with a rational
point is $k$-isomorphic to $\mathbb{P}^1_k$. -/


-- created on 2026-10-23
