import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.KWLoopWeight
open StatMech StatMech.Onsager


/--
[ons_loopWeight_KW_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWLoopWeight.lean)
-/
@[path]
private lemma ons_loopWeight_KW_eq_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x ω : ℂ}
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
-- imply
  ons_loopWeight (ons_KWmat L x ω) v = x ^ n * ∏ k : Fin n, ons_turnW ω (v (k + 1)).2 (v k).2 := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_KW_eq x ω v hvalid

/--
[ons_rev_nonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWLoopWeight.lean)
-/
@[path]
private lemma ons_rev_nonUturn_eq
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4}
-- given
  (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2) :
-- imply
  ∀ k : Fin n, (fun j => d (Fin.rev j) + 2) k.succ ≠ (fun j => d (Fin.rev j) + 2) k.castSucc + 2 := by
-- proof
  apply StatMech.Onsager.ons_rev_nonUturn n d hnu

/--
[ons_walk_prod_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWLoopWeight.lean)
-/
@[path]
private lemma ons_walk_prod_rev_eq
  {ω : ℂ}
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4}
-- given
  (hω : ω ≠ 0)
  (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2) :
-- imply
  ∏ k : Fin n, ons_turnW ω ((fun j => d (Fin.rev j) + 2) k.castSucc) ((fun j => d (Fin.rev j) + 2) k.succ) = (∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ))⁻¹ := by
-- proof
  apply StatMech.Onsager.ons_walk_prod_rev ω hω n d hnu

/--
[ons_walk_prod_rev_antipodal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWLoopWeight.lean)
-/
@[path]
private lemma ons_walk_prod_rev_antipodal_eq
  {ω : ℂ}
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4}
-- given
  (hω : ω ≠ 0)
  (hI : ω ^ 2 = Complex.I)
  (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2)
  (hend : d (Fin.last n) = d 0 + 2) :
-- imply
  ∏ k : Fin n, ons_turnW ω ((fun j => d (Fin.rev j) + 2) k.castSucc) ((fun j => d (Fin.rev j) + 2) k.succ) = - ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ) := by
-- proof
  apply StatMech.Onsager.ons_walk_prod_rev_antipodal ω hω hI n d hnu hend


-- created on 2026-10-23
