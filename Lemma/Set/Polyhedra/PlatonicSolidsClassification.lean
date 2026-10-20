import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Polyhedra.PlatonicSolidsClassification
open MetaMathlibExt


/--
[platonic_solids_classification](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Polyhedra/PlatonicSolidsClassification.lean)
-/
@[path]
private lemma platonic_solids_classification_eq
  :
-- imply
  ((∀ (V E F p q : ℕ) (verts : Fin V → EuclideanSpace ℝ (Fin 3))
    (edgeEnds : Fin E → Fin V × Fin V) (faceVerts : Fin F → Fin p → Fin V)
    (body : Set (EuclideanSpace ℝ (Fin 3))) (l angleDiag : ℝ),
    0 < V → 0 < E → 0 < F → 3 ≤ p → 3 ≤ q → 0 < l → 0 < angleDiag →
    body = convexHull ℝ (Set.range verts) →
    Convex ℝ body →
    (∀ v : Fin V, verts v ∈ body) →
    (∀ v : Fin V, verts v ∉ convexHull ℝ (verts '' {w : Fin V | w ≠ v})) →
    (Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
    ∃ i j : Fin V, d = verts i - verts j}) = 3) →
    (∀ e : Fin E, dist (verts (edgeEnds e).1) (verts (edgeEnds e).2) = l) →
    (∀ f : Fin F, ∀ i j : Fin p,
    j.val = (i.val + 1) % p →
    dist (verts (faceVerts f i)) (verts (faceVerts f j)) = l) →
    (∀ f : Fin F, ∀ h i j : Fin p,
    h.val = (i.val + p - 1) % p → j.val = (i.val + 1) % p →
    dist (verts (faceVerts f h)) (verts (faceVerts f j)) = angleDiag) →
    (∀ f : Fin F, Function.Injective (faceVerts f)) →
    (∀ f : Fin F, ∀ k : Fin p,
    verts (faceVerts f k) ∉ convexHull ℝ
    (verts '' (Set.range (faceVerts f) \ {faceVerts f k}))) →
    (∀ f : Fin F, ∀ i₁ j₁ i₂ j₂ : Fin p,
    j₁.val = (i₁.val + 1) % p → j₂.val = (i₂.val + 1) % p →
    i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ →
    Disjoint (convexHull ℝ {verts (faceVerts f i₁), verts (faceVerts f j₁)})
    (convexHull ℝ {verts (faceVerts f i₂), verts (faceVerts f j₂)})) →
    (∀ f : Fin F, ∀ i j : Fin p,
    j.val = (i.val + 1) % p →
    ∃ e : Fin E, edgeEnds e = (faceVerts f i, faceVerts f j) ∨
    edgeEnds e = (faceVerts f j, faceVerts f i)) →
    (∀ e : Fin E, ∃ f : Fin F, ∃ i j : Fin p,
    j.val = (i.val + 1) % p ∧
    (edgeEnds e = (faceVerts f i, faceVerts f j) ∨
    edgeEnds e = (faceVerts f j, faceVerts f i))) →
    (∀ e : Fin E, Set.ncard {f : Fin F | ∃ i j : Fin p,
    j.val = (i.val + 1) % p ∧
    (edgeEnds e = (faceVerts f i, faceVerts f j) ∨
    edgeEnds e = (faceVerts f j, faceVerts f i))} = 2) →
    (∀ e : Fin E, convexHull ℝ {verts (edgeEnds e).1, verts (edgeEnds e).2} ⊆ body) →
    (∀ f : Fin F, convexHull ℝ (verts '' Set.range (faceVerts f)) ⊆ body) →
    (∀ f : Fin F, Module.finrank ℝ (Submodule.span ℝ {d : EuclideanSpace ℝ (Fin 3) |
    ∃ i j : Fin p, d = verts (faceVerts f i) - verts (faceVerts f j)}) ≤ 2) →
    (∀ f : Fin F, ∃ n : EuclideanSpace ℝ (Fin 3), ∃ c : ℝ,
    n ≠ 0 ∧ (∀ x ∈ body, inner (𝕜 := by
-- proof
  apply MetaMathlibExt.platonic_solids_classification


-- created on 2026-10-20
