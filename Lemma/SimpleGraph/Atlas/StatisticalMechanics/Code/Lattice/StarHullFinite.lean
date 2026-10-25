import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.StarHullFinite
open SimpleGraph Function Set StatMech StatMech.Lattice


/--
[shf_coord_mem_proj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullFinite.lean)
-/
@[path]
private lemma shf_coord_mem_proj_eq
  {K : Set (Site 2)}
  {x : Site 2}
-- given
  (hx : x ∈ ndt_StarHull K) :
-- imply
  ∀ i : Fin 2, x i ∈ (fun y => y i) '' K := by
-- proof
  apply StatMech.Lattice.shf_coord_mem_proj K hx

/--
[shf_starHull_subset_projBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullFinite.lean)
-/
@[path]
private lemma shf_starHull_subset_projBox_eq
  {K : Set (Site 2)} :
-- imply
  ndt_StarHull K ⊆ {x : Site 2 | ∀ i, x i ∈ (fun y => y i) '' K} := by
-- proof
  apply StatMech.Lattice.shf_starHull_subset_projBox K

/--
[starHull_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullFinite.lean)
-/
@[path]
private lemma starHull_finite_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  (ndt_StarHull K).Finite := by
-- proof
  apply StatMech.Lattice.starHull_finite K hK


-- created on 2026-10-23
