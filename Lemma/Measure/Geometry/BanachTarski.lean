import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Geometry.BanachTarski
open MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
open FinitelyEquidecomposableByIsometries


/--
[finitelyEquidecomposableByIsometries_iff_bijOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma finitelyEquidecomposableByIsometries_iff_bijOn_eq
  [MetricSpace X]
  {A B : Set X} :
-- imply
  FinitelyEquidecomposableByIsometries A B ↔
    ∃ (f : X → X) (S : Set (X ≃ᵢ X)),
    S.Finite ∧ Set.BijOn f A B ∧ ∀ x ∈ A, ∃ g ∈ S, f x = g x := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.finitelyEquidecomposableByIsometries_iff_bijOn A B

/--
[refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma refl_eq
  [MetricSpace X]
  {A : Set X} :
-- imply
  FinitelyEquidecomposableByIsometries A A := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.FinitelyEquidecomposableByIsometries.refl A

/--
[symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma symm_eq
  [MetricSpace X]
  {A B : Set X}
-- given
  (h : FinitelyEquidecomposableByIsometries A B) :
-- imply
  FinitelyEquidecomposableByIsometries B A := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.FinitelyEquidecomposableByIsometries.symm h

/--
[trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma trans_eq
  [MetricSpace X]
  {A B C : Set X}
-- given
  (h0 : FinitelyEquidecomposableByIsometries A B)
  (h1 : FinitelyEquidecomposableByIsometries B C) :
-- imply
  FinitelyEquidecomposableByIsometries A C := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.FinitelyEquidecomposableByIsometries.trans h0 h1

/--
[union](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma union_eq
  [MetricSpace X]
  {A₁ A₂ B₁ B₂ : Set X}
-- given
  (h0 : FinitelyEquidecomposableByIsometries A₁ B₁)
  (h1 : FinitelyEquidecomposableByIsometries A₂ B₂)
  (hdA : Disjoint A₁ A₂)
  (hdB : Disjoint B₁ B₂) :
-- imply
  FinitelyEquidecomposableByIsometries (A₁ ∪ A₂) (B₁ ∪ B₂) := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.FinitelyEquidecomposableByIsometries.union h0 h1 hdA hdB

/--
[image_isometryEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma image_isometryEquiv_eq
  [MetricSpace X]
  {A : Set X}
-- given
  (g : X ≃ᵢ X) :
-- imply
  FinitelyEquidecomposableByIsometries A (g '' A) := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.FinitelyEquidecomposableByIsometries.image_isometryEquiv g A

/--
[banach_tarski_closedBall_unit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma banach_tarski_closedBall_unit_eq
  :
-- imply
  ∃ (c₁ c₂ : EuclideanSpace ℝ (Fin 3)),
    Disjoint (Metric.closedBall c₁ 1) (Metric.closedBall c₂ 1) ∧
    FinitelyEquidecomposableByIsometries
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (Metric.closedBall c₁ 1 ∪ Metric.closedBall c₂ 1) := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.banach_tarski_closedBall_unit


-- created on 2026-10-20
