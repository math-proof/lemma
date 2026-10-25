import Mathlib
import sympy.Basic
import Def.Geometry.TwoD
open scoped EuclideanGeometry Finset
open scoped EuclideanSpace EuclideanGeometry
open scoped Real
open EuclideanGeometry


namespace EuclideanGeometry

/--
[NonCollinearFor.subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
lemma NonCollinearFor.subset
  {n : ℕ}
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [MetricSpace P]
  [NormedAddTorsor V P]
  [Module.Oriented ℝ V (Fin 2)]
  [Fact (Module.finrank ℝ V = 2)]
  {p : Fin n → P}
  {n : ℕ}
  {S T : Set P}
-- given
  (h : S ⊆ T)
  (hS : NonCollinearFor n T) :
-- imply
  NonCollinearFor n S := by
-- proof
  intro A hA hFin hCard
  exact hS A (hA.trans h) hFin hCard

end EuclideanGeometry

namespace EuclideanGeometry

/--
[IsCcwConvexPolygon.sign_oangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
lemma IsCcwConvexPolygon.sign_oangle
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {n : ℕ}
  {p : Fin n → P}
  {i j k : Fin n}
-- given
  (hp : IsCcwConvexPolygon p)
  (hij : i < j)
  (hjk : j < k) :
-- imply
  (∡ (p i) (p j) (p k)).sign = -1 :=
-- proof
  hp hij hjk
set_option linter.docPrime false in

end EuclideanGeometry

namespace EuclideanGeometry

/--
[IsCcwConvexPolygon.sign_oangle'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
lemma IsCcwConvexPolygon.sign_oangle'
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
  rw [EuclideanGeometry.oangle_rotate_sign]
  exact hp hij hjk
set_option linter.docPrime false in

end EuclideanGeometry

namespace EuclideanGeometry

/--
[IsCcwConvexPolygon.sign_oangle''](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
lemma IsCcwConvexPolygon.sign_oangle''
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
  rw [← EuclideanGeometry.oangle_rotate_sign]
  exact hp hij hjk

end EuclideanGeometry

namespace EuclideanGeometry

/--
[IsCcwConvexPolygon.sign_oangle_finRotate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
lemma IsCcwConvexPolygon.sign_oangle_finRotate
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
  obtain ⟨n, rfl⟩ := le_iff_exists_add'.mp hn
  by_cases hi : i = Fin.last (n + 2)
  · rw [hi, finRotate_last, finRotate_apply_zero]
    exact hp.sign_oangle'' Fin.zero_lt_one Fin.one_lt_last
  by_cases hi' : finRotate _ i = Fin.last (n + 2)
  · rw [hi', finRotate_last]
    refine hp.sign_oangle' ?_ ((Fin.le_last _).lt_of_ne hi)
    rw [Fin.pos_iff_ne_zero]
    rintro rfl
    rw [finRotate_apply_zero] at hi'
    exact Fin.one_lt_last.ne hi'
  apply hp.sign_oangle <;> apply (lt_finRotate_iff_ne_last _).2 <;> assumption
@[simp] theorem isCcwConvexPolygon_zero (p : Fin 0 → P) : IsCcwConvexPolygon p := finZeroElim
@[simp] theorem isCcwConvexPolygon_one (p : Fin 1 → P) : IsCcwConvexPolygon p := by intro; omega
@[simp] theorem isCcwConvexPolygon_two (p : Fin 2 → P) : IsCcwConvexPolygon p := by intro; omega
set_option linter.docPrime false in

end EuclideanGeometry

namespace EuclideanGeometry

/--
[isCcwConvexPolygon_four'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
lemma isCcwConvexPolygon_four'
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {p : Fin 4 → P} :
-- imply
  IsCcwConvexPolygon p ↔ (∡ (p 0) (p 1) (p 2)).sign = -1 ∧ (∡ (p 1) (p 2) (p 3)).sign = -1 ∧
    (∡ (p 2) (p 3) (p 0)).sign = -1 ∧ (∡ (p 3) (p 0) (p 1)).sign = -1 := by
-- proof
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2, h3, h4⟩ ↦ ?_⟩
  · obtain ⟨h01, h12, h23⟩ : (0 : Fin 4) < 1 ∧ (1 : Fin 4) < 2 ∧ (2 : Fin 4) < 3 := by simp
    · repeat' constructor
      · exact h.sign_oangle h01 h12
      · exact h.sign_oangle h12 h23
      · exact h.sign_oangle' (h01.trans h12) h23
      · exact h.sign_oangle'' h01 (h12.trans h23)
  · intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk
    · exact h1
    · rw [EuclideanGeometry.oangle_rotate_sign]
      exact h4
    · rw [← EuclideanGeometry.oangle_rotate_sign]
      exact h3
    · exact h2

end EuclideanGeometry

namespace EuclideanGeometry

/--
[isCcwConvexPolygon_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
lemma isCcwConvexPolygon_four
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {A B C D : P} :
-- imply
  IsCcwConvexPolygon ![A, B, C, D] ↔
    (∡ A B C).sign = -1 ∧ (∡ B C D).sign = -1 ∧ (∡ C D A).sign = -1 ∧ (∡ D A B).sign = -1 :=
-- proof
  isCcwConvexPolygon_four'

end EuclideanGeometry

namespace EuclideanGeometry

/--
[isConvexPolygon_three_of_affineIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
lemma isConvexPolygon_three_of_affineIndependent
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {A B C : P}
-- given
  (hABC : AffineIndependent ℝ ![A, B, C]) :
-- imply
  IsConvexPolygon ![A, B, C] := by
-- proof
  rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.sign_ne_zero_iff] at hABC
  cases hsABC : (∡ A B C).sign
  · exact (hABC hsABC).elim
  · left
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk
    exact hsABC
  · right
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk
    rw [EuclideanGeometry.oangle_rev, Real.Angle.sign_neg, neg_eq_iff_eq_neg]
    exact (oangle_rotate_sign A B C).trans hsABC

end EuclideanGeometry

namespace EuclideanGeometry

/--
[isConvexPolygon_three_iff_affineIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
lemma isConvexPolygon_three_iff_affineIndependent
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {A B C : P} :
-- imply
  IsConvexPolygon ![A, B, C] ↔ AffineIndependent ℝ ![A, B, C] := by
-- proof
  refine ⟨fun h => ?_, isConvexPolygon_three_of_affineIndependent⟩
  rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.sign_ne_zero_iff]
  let p := ![A, B, C]
  change IsConvexPolygon p at h
  change Real.Angle.sign (∡ (p 0) (p 1) (p 2)) ≠ 0
  cases h with
  | inl h =>
    rw [h.sign_oangle (by simp) (by simp)]
    rintro ⟨⟩
  | inr h =>
    suffices Real.Angle.sign (∡ (p 0) (p 2) (p 1)) = -1 by
      rw [← oangle_swap₂₃_sign, this]; rintro ⟨⟩
    exact h.sign_oangle (i := 0) (j := 1) (k := 2) (by simp) (by simp)

end EuclideanGeometry

namespace EuclideanGeometry

/--
[isConvexPolygon_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
lemma isConvexPolygon_triangle
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {t : Affine.Triangle ℝ P} :
-- imply
  IsConvexPolygon t.points := by
-- proof
  have : t.points = ![t.points 0, t.points 1, t.points 2] := by ext i; fin_cases i <;> rfl
  rwa [this, isConvexPolygon_three_iff_affineIndependent, ← this]

end EuclideanGeometry

namespace EuclideanGeometry

/--
[orientedTriangleArea_eq_det](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
lemma orientedTriangleArea_eq_det
  {n : ℕ}
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [MetricSpace P]
  [NormedAddTorsor V P]
  [Module.Oriented ℝ V (Fin 2)]
  [Fact (Module.finrank ℝ V = 2)]
  {p : Fin n → P}
  {a b c : ℝ²} :
-- imply
  orientedTriangleArea a b c = Matrix.det !![a 0, b 0, c 0; a 1, b 1, c 1; 1, 1, 1] / 2 := by
-- proof
  rw [orientedTriangleArea, Orientation.areaForm_to_volumeForm,
    positiveOrientation.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
    Module.Basis.det_apply]
  suffices (a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1) =
    a 0 * b 1 - a 0 * c 1 - b 0 * a 1 + b 0 * c 1 + c 0 * a 1 - c 0 * b 1 by
    simp [Matrix.det_fin_two, Matrix.det_fin_three, Module.Basis.toMatrix, this]
  ring

end EuclideanGeometry

/--
[Set.IsIsoscelesFree.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
lemma Set.IsIsoscelesFree.mono
  [Dist α]
  {s t : Set α}
-- given
  (h : t ⊆ s)
  (hs : s.IsIsoscelesFree) :
-- imply
  t.IsIsoscelesFree :=
-- proof
  Set.Triplewise.mono h hs

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
[IsCcwConvexPolygon.sign_oangle'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean)
-/
@[path]
private lemma sign_oangle'_eq
  {n : ℕ}
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [MetricSpace P]
  [NormedAddTorsor V P]
  [Module.Oriented ℝ V (Fin 2)]
  [Fact (Module.finrank ℝ V = 2)]
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
private lemma sign_oangle''_eq
  {n : ℕ}
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [MetricSpace P]
  [NormedAddTorsor V P]
  [Module.Oriented ℝ V (Fin 2)]
  [Fact (Module.finrank ℝ V = 2)]
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


-- created on 2026-10-20
-- updated on 2026-10-23
