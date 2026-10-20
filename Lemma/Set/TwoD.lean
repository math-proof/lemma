import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.TwoD
open scoped EuclideanGeometry Finset
open scoped EuclideanSpace EuclideanGeometry
open scoped Real
open EuclideanGeometry


/--
[IsCcwConvexPolygon.sign_oangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma IsCcwConvexPolygon_sign_oangle_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {n : ℕ}
  {p : Fin n → P}
  {i j k : Fin n}
-- given
  (hp : IsCcwConvexPolygon p)
  (hij : i < j)
  (hjk : j < k) :
-- imply
  (∡ (p i) (p j) (p k)).sign = -1 := by
-- proof
  apply EuclideanGeometry.IsCcwConvexPolygon.sign_oangle hp hij hjk

/--
[IsCcwConvexPolygon.sign_oangle'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma IsCcwConvexPolygon_sign_oangle'_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {n : ℕ}
  {p : Fin n → P}
  {i j k : Fin n}
-- given
  (hp : IsCcwConvexPolygon p)
  (hij : i < j)
  (hjk : j < k) :
-- imply
  (∡ (p j) (p k) (p i)).sign = -1 := by
-- proof
  apply EuclideanGeometry.IsCcwConvexPolygon.sign_oangle' hp hij hjk

/--
[IsCcwConvexPolygon.sign_oangle''](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma IsCcwConvexPolygon_sign_oangle''_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {n : ℕ}
  {p : Fin n → P}
  {i j k : Fin n}
-- given
  (hp : IsCcwConvexPolygon p)
  (hij : i < j)
  (hjk : j < k) :
-- imply
  (∡ (p k) (p i) (p j)).sign = -1 := by
-- proof
  apply EuclideanGeometry.IsCcwConvexPolygon.sign_oangle'' hp hij hjk

/--
[IsCcwConvexPolygon.sign_oangle_finRotate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma IsCcwConvexPolygon_sign_oangle_finRotate_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {n : ℕ}
  {p : Fin n → P}
  {i : Fin n}
-- given
  (hp : IsCcwConvexPolygon p)
  (hn : 3 ≤ n) :
-- imply
  (∡ (p i) (p <| finRotate _ i) (p <| finRotate _ (finRotate _ i))).sign = -1 := by
-- proof
  apply EuclideanGeometry.IsCcwConvexPolygon.sign_oangle_finRotate hp hn i

/--
[isCcwConvexPolygon_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma isCcwConvexPolygon_zero_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {p : Fin 0 → P} :
-- imply
  IsCcwConvexPolygon p := by
-- proof
  apply EuclideanGeometry.isCcwConvexPolygon_zero p

/--
[isCcwConvexPolygon_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma isCcwConvexPolygon_one_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {p : Fin 1 → P} :
-- imply
  IsCcwConvexPolygon p := by
-- proof
  apply EuclideanGeometry.isCcwConvexPolygon_one p

/--
[isCcwConvexPolygon_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma isCcwConvexPolygon_two_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {p : Fin 2 → P} :
-- imply
  IsCcwConvexPolygon p := by
-- proof
  apply EuclideanGeometry.isCcwConvexPolygon_two p

/--
[isCcwConvexPolygon_four'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma isCcwConvexPolygon_four'_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {p : Fin 4 → P} :
-- imply
  IsCcwConvexPolygon p ↔ (∡ (p 0) (p 1) (p 2)).sign = -1 ∧ (∡ (p 1) (p 2) (p 3)).sign = -1 ∧
    (∡ (p 2) (p 3) (p 0)).sign = -1 ∧ (∡ (p 3) (p 0) (p 1)).sign = -1 := by
-- proof
  apply EuclideanGeometry.isCcwConvexPolygon_four'

/--
[isCcwConvexPolygon_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma isCcwConvexPolygon_four_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {A B C D : P} :
-- imply
  IsCcwConvexPolygon ![A, B, C, D] ↔
    (∡ A B C).sign = -1 ∧ (∡ B C D).sign = -1 ∧ (∡ C D A).sign = -1 ∧ (∡ D A B).sign = -1 := by
-- proof
  apply EuclideanGeometry.isCcwConvexPolygon_four A B C D

/--
[isConvexPolygon_three_of_affineIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma isConvexPolygon_three_of_affineIndependent_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {A B C : P}
-- given
  (hABC : AffineIndependent ℝ ![A, B, C]) :
-- imply
  IsConvexPolygon ![A, B, C] := by
-- proof
  apply EuclideanGeometry.isConvexPolygon_three_of_affineIndependent hABC

/--
[isConvexPolygon_three_iff_affineIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma isConvexPolygon_three_iff_affineIndependent_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {A B C : P} :
-- imply
  IsConvexPolygon ![A, B, C] ↔ AffineIndependent ℝ ![A, B, C] := by
-- proof
  apply EuclideanGeometry.isConvexPolygon_three_iff_affineIndependent

/--
[isConvexPolygon_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma isConvexPolygon_triangle_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {t : Affine.Triangle ℝ P} :
-- imply
  IsConvexPolygon t.points := by
-- proof
  apply EuclideanGeometry.isConvexPolygon_triangle t

/--
[Set.IsIsoscelesFree.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma Set_IsIsoscelesFree_mono_eq
  [Dist α]
  {s t : Set α}
-- given
  (h : t ⊆ s)
  (hs : s.IsIsoscelesFree) :
-- imply
  t.IsIsoscelesFree := by
-- proof
  apply Set.IsIsoscelesFree.mono h hs


-- created on 2026-10-20
