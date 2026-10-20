import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Convex.ColorfulCaratheodory
open MathlibExt.Geometry.Convex.ColorfulCaratheodoryWanted


/--
[colorful_caratheodory_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/ColorfulCaratheodory.lean)
-/
@[path]
private lemma colorful_caratheodory_finrank_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {m : ℕ}
  {S : Fin m → Finset V}
-- given
  (hm : Module.finrank ℝ V + 1 = m)
  (h0 : ∀ l, (0 : V) ∈ convexHull ℝ ((S l : Finset V) : Set V)) :
-- imply
  ∃ t : (l : Fin m) → ↥(S l),
    (0 : V) ∈ convexHull ℝ (Set.range fun l => ((t l : V))) := by
-- proof
  apply MathlibExt.Geometry.Convex.ColorfulCaratheodoryWanted.colorful_caratheodory_finrank hm S h0

/--
[colorful_caratheodory](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/ColorfulCaratheodory.lean)
-/
@[path]
private lemma colorful_caratheodory_eq
  {d : ℕ}
  {S : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d))}
-- given
  (hfin : ∀ i, (S i).Finite)
  (hmem : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (S i)) :
-- imply
  ∃ (choice : Fin (d + 1) → EuclideanSpace ℝ (Fin d)),
    (∀ i, choice i ∈ S i) ∧
    (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (Set.range choice) := by
-- proof
  apply MathlibExt.Geometry.Convex.ColorfulCaratheodoryWanted.colorful_caratheodory S hfin hmem

/--
[exists_colorful_mem_convexHull](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/ColorfulCaratheodory.lean)
-/
@[path]
private lemma exists_colorful_mem_convexHull_eq
  {d : ℕ}
  {S : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d))}
-- given
  (hmem : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (S i)) :
-- imply
  ∃ (choice : Fin (d + 1) → EuclideanSpace ℝ (Fin d)),
    (∀ i, choice i ∈ S i) ∧
    (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (Set.range choice) := by
-- proof
  apply MathlibExt.Geometry.Convex.ColorfulCaratheodoryWanted.exists_colorful_mem_convexHull S hmem


-- created on 2026-10-20
