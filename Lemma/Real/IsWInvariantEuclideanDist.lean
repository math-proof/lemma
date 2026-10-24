import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.CanonicalMetric
open Set AffineCoxeter
open scoped InnerProductSpace


namespace AffineCoxeter

/--
[euclideanDist_isWInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean)
-/
@[path]
private lemma euclideanDist_isWInvariant
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E} :
-- imply
  IsWInvariant W euclideanDist := by
-- proof
  intro w hw x y
  simp only [euclideanDist]
  have : dist (w x) (w y) = dist x y := AffineIsometryEquiv.dist_map w x y
  simp only [dist_eq_norm] at this
  exact this

end AffineCoxeter

namespace AffineCoxeter

/--
[AffineCoxeterComplex.nonempty_V](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean)
-/
@[path]
private lemma AffineCoxeterComplex.nonempty_V
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {A : AffineCoxeterComplex E} :
-- imply
  Nonempty A.V := by
-- proof
  by_contra hemp
  rw [not_nonempty_iff] at hemp
  have hrng : (Set.range A.vertexMap) = ∅ := by
    ext x; constructor
    · rintro ⟨v, _⟩; exact (hemp.false v).elim
    · intro h; exact h.elim
  have hspan := A.affineSpan_vertexMap_eq_top
  rw [hrng, AffineSubspace.span_empty] at hspan
  exact bot_ne_top hspan

end AffineCoxeter

namespace AffineCoxeter

/--
[inner_preservation_from_gram_matching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean)
-/
@[path]
private lemma inner_preservation_from_gram_matching
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {n : ℕ}
  [NormedAddCommGroup E']
  [InnerProductSpace ℝ E']
  {b : Module.Basis (Fin n) ℝ E}
  {b' : Module.Basis (Fin n) ℝ E'}
  {Ψ : E →ₗ[ℝ] E'}
-- given
  (hgram : ∀ i j : Fin n, @inner ℝ E' _ (b' i) (b' j) = @inner ℝ E _ (b i) (b j))
  (hΨ : ∀ i : Fin n, Ψ (b i) = b' i) :
-- imply
  ∀ x y : E, @inner ℝ E' _ (Ψ x) (Ψ y) = @inner ℝ E _ x y := by
-- proof
  intro x y
  conv_lhs => rw [show x = ∑ i : Fin n, b.equivFun x i • b i from (b.sum_equivFun x).symm]
  conv_lhs => rw [show y = ∑ i : Fin n, b.equivFun y i • b i from (b.sum_equivFun y).symm]
  simp only [map_sum, map_smul, hΨ]
  simp_rw [sum_inner (𝕜 := ℝ), inner_sum (𝕜 := ℝ), inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  conv_rhs => rw [show x = ∑ i : Fin n, b.equivFun x i • b i from (b.sum_equivFun x).symm]
  conv_rhs => rw [show y = ∑ i : Fin n, b.equivFun y i • b i from (b.sum_equivFun y).symm]
  simp_rw [sum_inner (𝕜 := ℝ), inner_sum (𝕜 := ℝ), inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  congr 1; ext i; congr 1; ext j; rw [hgram]

end AffineCoxeter

namespace AffineCoxeter

/--
[norm_of_inner_preserving_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean)
-/
@[path]
private lemma norm_of_inner_preserving_map
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E']
  [InnerProductSpace ℝ E']
  {Ψ : E →ₗ[ℝ] E'}
-- given
  (h : ∀ x y : E, @inner ℝ E' _ (Ψ x) (Ψ y) = @inner ℝ E _ x y) :
-- imply
  ∀ v : E, ‖Ψ v‖ = ‖v‖ := by
-- proof
  intro v
  have h1 : ‖Ψ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (F := E') (Ψ v)]
    rw [← real_inner_self_eq_norm_sq (F := E) v]
    exact h v v
  nlinarith [norm_nonneg (Ψ v), norm_nonneg v, sq_nonneg (‖Ψ v‖ - ‖v‖)]

end AffineCoxeter

namespace AffineCoxeter

/--
[SimplicialComplexIso.injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean)
-/
@[path]
private lemma SimplicialComplexIso.injective
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [DecidableEq V']
  [DecidableEq W']
  {K : SimplicialComplex V'}
  {L : SimplicialComplex W'}
  {φ : SimplicialComplexIso K L} :
-- imply
  Function.Injective φ.toMorphism.toFun :=
-- proof
  Function.HasLeftInverse.injective ⟨φ.invMorphism.toFun, φ.left_inv⟩

end AffineCoxeter

namespace AffineCoxeter

/--
[SimplicialComplexIso.maps_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean)
-/
@[path]
private lemma SimplicialComplexIso.maps_maximal
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [DecidableEq V']
  [DecidableEq W']
  {K : SimplicialComplex V'}
  {L : SimplicialComplex W'}
  {φ : SimplicialComplexIso K L}
  {C : Finset V'}
-- given
  (hC : K.IsMaximal C) :
-- imply
  L.IsMaximal (C.image φ.toMorphism.toFun) := by
-- proof
  refine ⟨φ.toMorphism.map_face C hC.1, ?_⟩
  intro D hD hCD
  have hD_inv := φ.invMorphism.map_face D hD
  have hC_sub : C ⊆ D.image φ.invMorphism.toFun := by
    intro v hv
    have := hCD (Finset.mem_image_of_mem _ hv)
    exact Finset.mem_image.mpr ⟨φ.toMorphism.toFun v, this, φ.left_inv v⟩
  have := hC.2 _ hD_inv hC_sub
  rw [this]; ext w; simp only [Finset.mem_image]
  exact ⟨fun ⟨v, ⟨u, hu, huv⟩, hvw⟩ => by rw [← huv, φ.right_inv] at hvw; rwa [← hvw],
    fun hw => ⟨φ.invMorphism.toFun w, ⟨w, hw, rfl⟩, φ.right_inv w⟩⟩

end AffineCoxeter

namespace AffineCoxeter

/--
[coxeter_iso_dim_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean)
-/
@[path]
private lemma coxeter_iso_dim_eq
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E']
  [InnerProductSpace ℝ E']
  {A : AffineCoxeterComplex E}
  {A' : AffineCoxeterComplex E'}
  {φ : SimplicialComplexIso A.complex A'.complex} :
-- imply
  A.n = A'.n := by
-- proof
  obtain ⟨C, hC⟩ := A.exists_chamber
  have h1 := A.chamber_card C hC
  have h2 := A'.chamber_card _ (φ.maps_maximal C hC)
  have h3 := Finset.card_image_of_injective C φ.injective
  omega

end AffineCoxeter

namespace AffineCoxeter

/--
[iso_chamber_count_preserved](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean)
-/
@[path]
private lemma iso_chamber_count_preserved
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [DecidableEq V']
  [DecidableEq W']
  {K : SimplicialComplex V'}
  {L : SimplicialComplex W'}
  {φ : SimplicialComplexIso K L}
  {F : Finset V'} :
-- imply
  Set.ncard {D | L.IsMaximal D ∧ F.image φ.toMorphism.toFun ⊆ D} = Set.ncard {C | K.IsMaximal C ∧ F ⊆ C} := by
-- proof
  suffices h : (fun C => C.image φ.toMorphism.toFun) '' {C | K.IsMaximal C ∧ F ⊆ C} =
    {D | L.IsMaximal D ∧ F.image φ.toMorphism.toFun ⊆ D} by
    rw [← h]
    exact Set.ncard_image_of_injective _ (fun _ _ h => Finset.image_injective φ.injective h)
  ext D
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, ⟨hCmax, hFC⟩, rfl⟩
    exact ⟨φ.maps_maximal C hCmax, Finset.image_subset_image hFC⟩
  · rintro ⟨hDmax, hFD⟩
    refine ⟨D.image φ.invMorphism.toFun, ⟨φ.symm.maps_maximal D hDmax, ?_⟩, ?_⟩
    ·
      intro v hv
      have hφv : φ.toMorphism.toFun v ∈ D := hFD (Finset.mem_image_of_mem _ hv)
      exact Finset.mem_image.mpr ⟨φ.toMorphism.toFun v, hφv, φ.left_inv v⟩
    ·
      rw [Finset.image_image]
      have : φ.toMorphism.toFun ∘ φ.invMorphism.toFun = id := funext φ.right_inv
      rw [this, Finset.image_id]

end AffineCoxeter

namespace AffineCoxeter

/--
[vertex_compatible_map_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean)
-/
@[path]
private lemma vertex_compatible_map_unique
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E']
  [InnerProductSpace ℝ E']
  {A : AffineCoxeterComplex E}
  {A' : AffineCoxeterComplex E'}
  {φ : SimplicialComplexIso A.complex A'.complex}
  {f g : AffineMap ℝ E E'}
-- given
  (hf : ∀ v, f (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v))
  (hg : ∀ v, g (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v)) :
-- imply
  f = g := by
-- proof
  ext x
  have h_eqon : Set.EqOn f g (Set.range A.vertexMap) := by
    intro y hy
    obtain ⟨v, rfl⟩ := hy
    rw [hf v, hg v]
  have h_span := AffineMap.eqOn_affineSpan h_eqon
  have hx : x ∈ (affineSpan ℝ (Set.range A.vertexMap) : Set E) := by
    rw [A.affineSpan_vertexMap_eq_top]; trivial
  exact h_span hx

end AffineCoxeter

namespace AffineCoxeter

/--
[normalizedDist_isWInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean)
-/
@[path]
private lemma normalizedDist_isWInvariant
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {A : AffineCoxeterComplex E} :
-- imply
  IsWInvariant A.W (normalizedDist A) := by
-- proof
  intro w hw x y
  simp only [normalizedDist]
  rw [euclideanDist_isWInvariant A.W w hw x y]
/-- The canonical (chamber-diameter-normalized) metric is an isometry invariant of
the simplicial structure: any affine map $f$ extending an iso $\varphi$ preserves the
normalized Euclidean distance. This is the main result of Section 13.7. -/
end AffineCoxeter



-- created on 2026-10-23
-- updated on 2026-10-24
