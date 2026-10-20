import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.JaccardLattice
open JaccardLattice


/--
[gilbertCondition_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/JaccardLattice.lean)
-/
@[path]
private lemma gilbertCondition_iff_eq
  [Lattice L]
  {f : L → ℝ} :
-- imply
  GilbertCondition f ↔ IsModularValuation f ∧ Monotone f := by
-- proof
  apply JaccardLattice.gilbertCondition_iff

/--
[jaccardDist_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/JaccardLattice.lean)
-/
@[path]
private lemma jaccardDist_eq_div_eq
  [Lattice L]
  {f : L → ℝ}
  {X Y : L}
-- given
  (hpos : IsStrictlyPositive f) :
-- imply
  jaccardDist f X Y = (f (X ⊔ Y) - f (X ⊓ Y)) / f (X ⊔ Y) := by
-- proof
  apply JaccardLattice.jaccardDist_eq_div hpos X Y

/--
[jaccardDist_triangle_of_gilbertCondition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/JaccardLattice.lean)
-/
@[path]
private lemma jaccardDist_triangle_of_gilbertCondition_eq
  [Lattice L]
  {f : L → ℝ}
  {U V W : L}
-- given
  (hG : GilbertCondition f)
  (hpos : IsStrictlyPositive f) :
-- imply
  jaccardDist f U W + jaccardDist f W V ≥ jaccardDist f U V := by
-- proof
  apply JaccardLattice.jaccardDist_triangle_of_gilbertCondition hG hpos U V W

/--
[jaccardDist_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/JaccardLattice.lean)
-/
@[path]
private lemma jaccardDist_triangle_eq
  [Lattice L]
  {f : L → ℝ}
  {U V W : L}
-- given
  (hM : IsModularValuation f)
  (hmono : Monotone f)
  (hpos : IsStrictlyPositive f) :
-- imply
  jaccardDist f U W + jaccardDist f W V ≥ jaccardDist f U V := by
-- proof
  apply JaccardLattice.jaccardDist_triangle hM hmono hpos U V W


-- created on 2026-10-20
