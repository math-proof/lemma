import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.JordanParity
open StatMech StatMech.Onsager StatMech.Onsager.JordanParity


/--
[upCross_vstep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JordanParity.lean)
-/
@[path]
private lemma upCross_vstep_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (h : ∀ k : Fin n, isHorizEdge (d k) → min ((pos d k).1) ((pos d (k+1)).1) = a → (pos d k).2 ≠ b + 1) :
-- imply
  upCross d a b = upCross d a (b + 1) := by
-- proof
  apply StatMech.Onsager.JordanParity.upCross_vstep d a b h

/--
[rayParity_vstep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JordanParity.lean)
-/
@[path]
private lemma rayParity_vstep_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (h : ∀ k : Fin n, isHorizEdge (d k) → min ((pos d k).1) ((pos d (k+1)).1) = a → (pos d k).2 ≠ b + 1) :
-- imply
  rayParity d a b = rayParity d a (b + 1) := by
-- proof
  apply StatMech.Onsager.JordanParity.rayParity_vstep d a b h

/--
[upCross_topOutside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JordanParity.lean)
-/
@[path]
private lemma upCross_topOutside_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b T : ℤ}
-- given
  (hT : ∀ j : Fin n, (pos d j).2 ≤ T)
  (hb : T ≤ b) :
-- imply
  upCross d a b = 0 := by
-- proof
  apply StatMech.Onsager.JordanParity.upCross_topOutside d a b T hT hb

/--
[rayParity_topOutside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JordanParity.lean)
-/
@[path]
private lemma rayParity_topOutside_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b T : ℤ}
-- given
  (hT : ∀ j : Fin n, (pos d j).2 ≤ T)
  (hb : T ≤ b) :
-- imply
  rayParity d a b = 0 := by
-- proof
  apply StatMech.Onsager.JordanParity.rayParity_topOutside d a b T hT hb

/--
[upCross_hstep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JordanParity.lean)
-/
@[path]
private lemma upCross_hstep_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hstr : ∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = a + 1 → ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ b ∧ b < max ((pos d k).2) ((pos d (k + 1)).2))) :
-- imply
  upCross d a b + upCross d (a + 1) b = 2 * (Finset.univ.filter (fun k : Fin n => ¬ ((pos d k).1 = a + 1 ∧ b + 1 ≤ (pos d k).2) ∧ ((pos d (k + 1)).1 = a + 1 ∧ b + 1 ≤ (pos d (k + 1)).2))).card := by
-- proof
  apply StatMech.Onsager.JordanParity.upCross_hstep d hclosed a b hstr

/--
[rayParity_hstep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JordanParity.lean)
-/
@[path]
private lemma rayParity_hstep_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hstr : ∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = a + 1 → ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ b ∧ b < max ((pos d k).2) ((pos d (k + 1)).2))) :
-- imply
  rayParity d a b = rayParity d (a + 1) b := by
-- proof
  apply StatMech.Onsager.JordanParity.rayParity_hstep d hclosed a b hstr


-- created on 2026-10-23
