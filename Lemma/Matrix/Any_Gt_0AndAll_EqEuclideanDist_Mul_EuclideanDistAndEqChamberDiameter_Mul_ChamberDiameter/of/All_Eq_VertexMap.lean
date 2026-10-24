import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.CoxeterSimilitude
open Set AffineCoxeter
open scoped InnerProductSpace


namespace AffineCoxeter

/--
[cor_affine_coxeter_similitude](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CoxeterSimilitude.lean)
-/
@[path]
lemma cor_affine_coxeter_similitude
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E']
  [InnerProductSpace ℝ E']
  {A : AffineCoxeterComplex E}
  {A' : AffineCoxeterComplex E'}
  {φ : SimplicialComplexIso A.complex A'.complex}
  {f : E →ᵃ[ℝ] E'}
-- given
  (hf_compat : ∀ v, f (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v)) :
-- imply
  ∃ (μ : ℝ), μ > 0 ∧ (∀ x y : E, euclideanDist (E := E') (f x) (f y) = μ * euclideanDist x y) ∧ A'.chamberDiameter = μ * A.chamberDiameter :=
-- proof
  simplicial_iso_is_similitude_with_diameter A A' φ f hf_compat

end AffineCoxeter

namespace AffineCoxeter

/--
[cor_affine_coxeter_isometry_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CoxeterSimilitude.lean)
-/
@[path]
lemma cor_affine_coxeter_isometry_normalized
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E']
  [InnerProductSpace ℝ E']
  {A : AffineCoxeterComplex E}
  {A' : AffineCoxeterComplex E'}
  {φ : SimplicialComplexIso A.complex A'.complex}
  {f : E →ᵃ[ℝ] E'}
-- given
  (hf_compat : ∀ v, f (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v)) :
-- imply
  ∀ x y : E, normalizedDist A' (f x) (f y) = normalizedDist A x y :=
-- proof
  canonical_metric_isometry A A' φ f hf_compat
end AffineCoxeter



-- created on 2026-10-23
