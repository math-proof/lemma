import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.RayFlipV
open StatMech StatMech.Onsager StatMech.Onsager.RayFlipV


/--
[upCross_vsplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RayFlipV.lean)
-/
@[path]
private lemma upCross_vsplit_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ} :
-- imply
  upCross d a b = upCross d a (b + 1) + (midSet d a (b + 1)).card := by
-- proof
  apply StatMech.Onsager.RayFlipV.upCross_vsplit d a b

/--
[rayParity_vflip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RayFlipV.lean)
-/
@[path]
private lemma rayParity_vflip_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (hodd : (midSet d a (b + 1)).card % 2 = 1) :
-- imply
  rayParity d a b = rayParity d a (b + 1) + 1 := by
-- proof
  apply StatMech.Onsager.RayFlipV.rayParity_vflip d a b hodd


-- created on 2026-10-23
