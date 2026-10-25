import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.RayFlipH
open StatMech StatMech.Onsager StatMech.Onsager.RayFlipH


/--
[upCross_hstep_gen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RayFlipH.lean)
-/
@[path]
private lemma upCross_hstep_gen_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  upCross d a b + upCross d (a + 1) b + (straddleSet d a b).card = 2 * (Finset.univ.filter (fun k : Fin n => ¬ ((pos d k).1 = a + 1 ∧ b + 1 ≤ (pos d k).2) ∧ ((pos d (k + 1)).1 = a + 1 ∧ b + 1 ≤ (pos d (k + 1)).2))).card := by
-- proof
  apply StatMech.Onsager.RayFlipH.upCross_hstep_gen d hclosed a b

/--
[rayParity_hstep_gen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RayFlipH.lean)
-/
@[path]
private lemma rayParity_hstep_gen_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  rayParity d a b + rayParity d (a + 1) b = ((straddleSet d a b).card : ZMod 2) := by
-- proof
  apply StatMech.Onsager.RayFlipH.rayParity_hstep_gen d hclosed a b

/--
[rayParity_hflip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RayFlipH.lean)
-/
@[path]
private lemma rayParity_hflip_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hodd : (straddleSet d a b).card % 2 = 1) :
-- imply
  rayParity d a b = rayParity d (a + 1) b + 1 := by
-- proof
  apply StatMech.Onsager.RayFlipH.rayParity_hflip d hclosed a b hodd


-- created on 2026-10-23
