import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ProjectiveIntersectionBound
open Ideal MvPolynomial Classical


/--
[affine_intersection_component_codim_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionBound.lean)
-/
@[path]
lemma affine_intersection_component_codim_bound
  [CommRing R]
  [IsNoetherianRing R]
  {s t : Finset R}
  {𝔴 : Ideal R}
-- given
  (hmin : 𝔴 ∈ (Ideal.span ((s ∪ t : Finset R) : Set R)).minimalPrimes) :
-- imply
  𝔴.height ≤ s.card + t.card := by
-- proof
  have h := height_le_card_of_mem_minimalPrimes_span_finset hmin
  refine le_trans h ?_
  rw [show (↑(s.card) : ℕ∞) + ↑(t.card) = ↑(s.card + t.card) from by push_cast; ring]
  exact ENat.coe_le_coe.mpr (Finset.card_union_le s t)

/--
[projective_cone_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionBound.lean)
-/
@[path]
lemma projective_cone_intersection
  [Field k]
  {n : ℕ}
  {𝔭 𝔮 : Ideal (MvPolynomial (Fin (n + 1)) k)}
-- given
  (hp : 𝔭 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
  (hq : 𝔮 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1))) :
-- imply
  𝔭 ⊔ 𝔮 ≠ ⊤ :=
-- proof
  MvPolynomial.sup_ne_top_of_le_variablesIdeal hp hq


-- created on 2026-10-23
