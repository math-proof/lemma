import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.DartInjective
open SimpleGraph StatMech StatMech.Lattice


/--
[rot90Fun_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma rot90Fun_injective_eq :
-- imply
  Function.Injective (rot90Fun : Site 2 → Site 2) := by
-- proof
  apply StatMech.Lattice.rot90Fun_injective

/--
[rot90Fun_rot90Fun'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma rot90Fun_rot90Fun'_eq
  {a : Site 2} :
-- imply
  rot90Fun (rot90Fun a) = -a := by
-- proof
  apply StatMech.Lattice.rot90Fun_rot90Fun' a

/--
[rot90Fun_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma rot90Fun_neg_eq
  {a : Site 2} :
-- imply
  rot90Fun (-a) = -rot90Fun a := by
-- proof
  apply StatMech.Lattice.rot90Fun_neg a

/--
[dartNext_right_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma dartNext_right_tail_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h : e.head + (-rot90Fun e.dir) ∈ K) :
-- imply
  (dartNext K e).tail = e.head + (-rot90Fun e.dir) := by
-- proof
  apply StatMech.Lattice.dartNext_right_tail K e h

/--
[dartNext_straight_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma dartNext_straight_tail_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : e.head + (-rot90Fun e.dir) ∉ K)
  (h1 : e.tail + (-rot90Fun e.dir) ∈ K) :
-- imply
  (dartNext K e).tail = e.tail + (-rot90Fun e.dir) := by
-- proof
  apply StatMech.Lattice.dartNext_straight_tail K e h0 h1

/--
[dartNext_straight_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma dartNext_straight_head_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : e.head + (-rot90Fun e.dir) ∉ K)
  (h1 : e.tail + (-rot90Fun e.dir) ∈ K) :
-- imply
  (dartNext K e).head = e.head + (-rot90Fun e.dir) := by
-- proof
  apply StatMech.Lattice.dartNext_straight_head K e h0 h1

/--
[dartNext_straight_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma dartNext_straight_dir_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : e.head + (-rot90Fun e.dir) ∉ K)
  (h1 : e.tail + (-rot90Fun e.dir) ∈ K) :
-- imply
  (dartNext K e).dir = e.dir := by
-- proof
  apply StatMech.Lattice.dartNext_straight_dir K e h0 h1

/--
[dartNext_left_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma dartNext_left_tail_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : e.head + (-rot90Fun e.dir) ∉ K)
  (h1 : e.tail + (-rot90Fun e.dir) ∉ K) :
-- imply
  (dartNext K e).tail = e.tail := by
-- proof
  apply StatMech.Lattice.dartNext_left_tail K e h0 h1

/--
[dartNext_left_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma dartNext_left_head_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : e.head + (-rot90Fun e.dir) ∉ K)
  (h1 : e.tail + (-rot90Fun e.dir) ∉ K) :
-- imply
  (dartNext K e).head = e.tail + (-rot90Fun e.dir) := by
-- proof
  apply StatMech.Lattice.dartNext_left_head K e h0 h1

/--
[dartNext_left_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma dartNext_left_dir_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : e.head + (-rot90Fun e.dir) ∉ K)
  (h1 : e.tail + (-rot90Fun e.dir) ∉ K) :
-- imply
  (dartNext K e).dir = -rot90Fun e.dir := by
-- proof
  apply StatMech.Lattice.dartNext_left_dir K e h0 h1

/--
[dart_eq_of_head_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma dart_eq_of_head_dir_eq
  {e₁ e₂ : Dart}
-- given
  (hH : e₁.head = e₂.head)
  (hd : e₁.dir = e₂.dir) :
-- imply
  e₁ = e₂ := by
-- proof
  apply StatMech.Lattice.dart_eq_of_head_dir hH hd

/--
[dart_eq_of_tail_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma dart_eq_of_tail_dir_eq
  {e₁ e₂ : Dart}
-- given
  (hT : e₁.tail = e₂.tail)
  (hd : e₁.dir = e₂.dir) :
-- imply
  e₁ = e₂ := by
-- proof
  apply StatMech.Lattice.dart_eq_of_tail_dir hT hd

/--
[eq_of_dartNext_eq_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma eq_of_dartNext_eq_right_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (a : e₁.head + (-rot90Fun e₁.dir) ∈ K)
  (b : e₂.head + (-rot90Fun e₂.dir) ∈ K)
  (heq : dartNext K e₁ = dartNext K e₂) :
-- imply
  e₁ = e₂ := by
-- proof
  apply StatMech.Lattice.eq_of_dartNext_eq_right K e₁ e₂ a b heq

/--
[eq_of_dartNext_eq_straight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma eq_of_dartNext_eq_straight_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (a1 : e₁.head + (-rot90Fun e₁.dir) ∉ K)
  (a2 : e₁.tail + (-rot90Fun e₁.dir) ∈ K)
  (b1 : e₂.head + (-rot90Fun e₂.dir) ∉ K)
  (b2 : e₂.tail + (-rot90Fun e₂.dir) ∈ K)
  (heq : dartNext K e₁ = dartNext K e₂) :
-- imply
  e₁ = e₂ := by
-- proof
  apply StatMech.Lattice.eq_of_dartNext_eq_straight K e₁ e₂ a1 a2 b1 b2 heq

/--
[eq_of_dartNext_eq_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma eq_of_dartNext_eq_left_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (a1 : e₁.head + (-rot90Fun e₁.dir) ∉ K)
  (a2 : e₁.tail + (-rot90Fun e₁.dir) ∉ K)
  (b1 : e₂.head + (-rot90Fun e₂.dir) ∉ K)
  (b2 : e₂.tail + (-rot90Fun e₂.dir) ∉ K)
  (heq : dartNext K e₁ = dartNext K e₂) :
-- imply
  e₁ = e₂ := by
-- proof
  apply StatMech.Lattice.eq_of_dartNext_eq_left K e₁ e₂ a1 a2 b1 b2 heq

/--
[not_dartNext_eq_right_straight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma not_dartNext_eq_right_straight_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (b1t : e₁.tail ∈ K)
  (b2h : e₂.head ∉ K)
  (hR : e₁.head + (-rot90Fun e₁.dir) ∈ K)
  (hS1 : e₂.head + (-rot90Fun e₂.dir) ∉ K)
  (hS2 : e₂.tail + (-rot90Fun e₂.dir) ∈ K)
  (heq : dartNext K e₁ = dartNext K e₂) :
-- imply
  False := by
-- proof
  apply StatMech.Lattice.not_dartNext_eq_right_straight K e₁ e₂ b1t b2h hR hS1 hS2 heq

/--
[not_dartNext_eq_right_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma not_dartNext_eq_right_left_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (b1t : e₁.tail ∈ K)
  (hR : e₁.head + (-rot90Fun e₁.dir) ∈ K)
  (hL1 : e₂.head + (-rot90Fun e₂.dir) ∉ K)
  (hL2 : e₂.tail + (-rot90Fun e₂.dir) ∉ K)
  (heq : dartNext K e₁ = dartNext K e₂) :
-- imply
  False := by
-- proof
  apply StatMech.Lattice.not_dartNext_eq_right_left K e₁ e₂ b1t hR hL1 hL2 heq

/--
[not_dartNext_eq_straight_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma not_dartNext_eq_straight_left_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (b1t : e₁.tail ∈ K)
  (b2h : e₂.head ∉ K)
  (hS1 : e₁.head + (-rot90Fun e₁.dir) ∉ K)
  (hS2 : e₁.tail + (-rot90Fun e₁.dir) ∈ K)
  (hL1 : e₂.head + (-rot90Fun e₂.dir) ∉ K)
  (hL2 : e₂.tail + (-rot90Fun e₂.dir) ∉ K)
  (heq : dartNext K e₁ = dartNext K e₂) :
-- imply
  False := by
-- proof
  apply StatMech.Lattice.not_dartNext_eq_straight_left K e₁ e₂ b1t b2h hS1 hS2 hL1 hL2 heq

/--
[dartNext_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma dartNext_injOn_eq
  {K : Set (Site 2)} :
-- imply
  Set.InjOn (dartNext K) {e | IsBoundaryDart K e} := by
-- proof
  apply StatMech.Lattice.dartNext_injOn K

/--
[unitVectors_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma unitVectors_finite_eq :
-- imply
  {z : Site 2 | unitWt z = 1}.Finite := by
-- proof
  apply StatMech.Lattice.unitVectors_finite

/--
[boundaryDarts_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma boundaryDarts_finite_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  {e : Dart | IsBoundaryDart K e}.Finite := by
-- proof
  apply StatMech.Lattice.boundaryDarts_finite K hK

/--
[dartNext_bijOn_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartInjective.lean)
-/
@[path]
private lemma dartNext_bijOn_of_finite_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  Set.BijOn (dartNext K) {e | IsBoundaryDart K e} {e | IsBoundaryDart K e} := by
-- proof
  apply StatMech.Lattice.dartNext_bijOn_of_finite K hK


-- created on 2026-10-23
