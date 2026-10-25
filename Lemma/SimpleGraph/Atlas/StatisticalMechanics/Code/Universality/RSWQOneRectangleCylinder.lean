import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWQOneRectangleCylinder
open Set SimpleGraph MeasureTheory StatMech StatMech.Universality


/--
[rq1_rect_subset_box_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneRectangleCylinder.lean)
-/
@[path]
private lemma rq1_rect_subset_box_of_bounds_eq
  {N : ℕ}
  {a b c d : ℤ}
-- given
  (ha : -(N : ℤ) ≤ a)
  (hb : b ≤ (N : ℤ))
  (hc : -(N : ℤ) ≤ c)
  (hd : d ≤ (N : ℤ)) :
-- imply
  rect a b c d ⊆ box 2 N := by
-- proof
  apply StatMech.Universality.rq1_rect_subset_box_of_bounds ha hb hc hd

/--
[rq1_finiteRectangleEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneRectangleCylinder.lean)
-/
@[path]
private lemma rq1_finiteRectangleEvent_dependsOn_eq
  {N : ℕ}
  {a b c d : ℤ}
-- given
  (hrect : rect a b c d ⊆ box 2 N) :
-- imply
  _root_.DependsOn ((rq1_finiteRectangleEvent N a b c d).indicator (fun _ => (1 : ℝ))) ((boxGraph 2 N).edgeFinset : Set (Sym2 (boxVerts 2 N))) := by
-- proof
  apply StatMech.Universality.rq1_finiteRectangleEvent_dependsOn N a b c d hrect

/--
[rq1_finiteRectangleEvent_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneRectangleCylinder.lean)
-/
@[path]
private lemma rq1_finiteRectangleEvent_preimage_eq
  {N : ℕ}
  {a b c d : ℤ}
-- given
  (hrect : rect a b c d ⊆ box 2 N) :
-- imply
  boxRestrict 2 N ⁻¹' rq1_finiteRectangleEvent N a b c d = horizontalCrossingEvent a b c d := by
-- proof
  apply StatMech.Universality.rq1_finiteRectangleEvent_preimage N a b c d hrect

/--
[rq1_wiredInfiniteVolume_rectangle_eq_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneRectangleCylinder.lean)
-/
@[path]
private lemma rq1_wiredInfiniteVolume_rectangle_eq_bernoulli_eq
  {N : ℕ}
  {a b c d : ℤ}
  {p : ℝ}
-- given
  (hrect : rect a b c d ⊆ box 2 N)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredInfiniteVolume 2 hp hp1 (by norm_num : (0 : ℝ) < 1) : Measure (ConfigSpace (Sym2 (Site 2)))).real (horizontalCrossingEvent a b c d) = (bernoulliProductMeasure (E := Sym2 (Site 2)) (⟨p, hp.le⟩ : ℝ≥0) (by exact_mod_cast hp1.le)).real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rq1_wiredInfiniteVolume_rectangle_eq_bernoulli N a b c d hrect hp hp1

/--
[rq1_wiredInfiniteVolume_rectangle_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneRectangleCylinder.lean)
-/
@[path]
private lemma rq1_wiredInfiniteVolume_rectangle_eq_eq
  {N : ℕ}
  {a b c d : ℤ}
-- given
  (hrect : rect a b c d ⊆ box 2 N) :
-- imply
  (wiredInfiniteVolume 2 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1) (by norm_num : (0 : ℝ) < 1) : Measure (ConfigSpace (Sym2 (Site 2)))).real (horizontalCrossingEvent a b c d) = rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rq1_wiredInfiniteVolume_rectangle_eq N a b c d hrect

/--
[rq1_wiredInfiniteVolume_square_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneRectangleCylinder.lean)
-/
@[path]
private lemma rq1_wiredInfiniteVolume_square_half_eq
  {N : ℕ}
  {a c m : ℤ}
-- given
  (hm : 0 < m)
  (hrect : rect a (a + m) c (c + m) ⊆ box 2 N) :
-- imply
  (1 : ℝ) / 2 ≤ (wiredInfiniteVolume 2 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1) (by norm_num : (0 : ℝ) < 1) : Measure (ConfigSpace (Sym2 (Site 2)))).real (horizontalCrossingEvent a (a + m) c (c + m)) := by
-- proof
  apply StatMech.Universality.rq1_wiredInfiniteVolume_square_half N a c m hm hrect


-- created on 2026-10-23
