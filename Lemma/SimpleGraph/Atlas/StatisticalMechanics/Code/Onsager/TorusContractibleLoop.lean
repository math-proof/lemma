import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.TorusContractibleLoop
open StatMech StatMech.Onsager


/--
[ons_stepOf_eq_exponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_stepOf_eq_exponents_eq
  {mu : Fin 4} :
-- imply
  stepOf mu = (ons_dirExponentX mu, ons_dirExponentY mu) := by
-- proof
  apply StatMech.Onsager.ons_stepOf_eq_exponents mu

/--
[ons_reduceSite_add_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_reduceSite_add_step_eq
  {L : ℕ}
  {p : ℤ × ℤ}
  {mu : Fin 4} :
-- imply
  ons_reduceSite L (p + stepOf mu) = ons_dirStep L mu (ons_reduceSite L p) := by
-- proof
  apply StatMech.Onsager.ons_reduceSite_add_step L p mu

/--
[ons_liftSite_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_liftSite_succ_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {k : Fin n}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
-- imply
  ons_liftSite v (k + 1) = ons_dirStep L (ons_liftDir v k) (ons_liftSite v k) := by
-- proof
  apply StatMech.Onsager.ons_liftSite_succ v hvalid k

/--
[ons_liftDir_sum_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_liftDir_sum_step_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L} :
-- imply
  ∑ k, stepOf (ons_liftDir v k) = ((∑ k, ons_dirExponentX (v k).2), ∑ k, ons_dirExponentY (v k).2) := by
-- proof
  apply StatMech.Onsager.ons_liftDir_sum_step v

/--
[ons_pos_succ_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_pos_succ_cast_eq
  {m : ℕ}
  {d : Fin (m + 1) → Fin 4}
  {i : Fin m} :
-- imply
  pos d i.succ = pos d i.castSucc + stepOf (d i.castSucc) := by
-- proof
  apply StatMech.Onsager.ons_pos_succ_cast d i

/--
[ons_liftSite_eq_reduce_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_liftSite_eq_reduce_pos_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {k : Fin n}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
-- imply
  ons_liftSite v k = ((ons_reduceSite L (pos (ons_liftDir v) k)).1 + (ons_liftSite v 0).1, (ons_reduceSite L (pos (ons_liftDir v) k)).2 + (ons_liftSite v 0).2) := by
-- proof
  apply StatMech.Onsager.ons_liftSite_eq_reduce_pos v hvalid k

/--
[ons_liftDir_pos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_liftDir_pos_injective_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k => (v k).1)) :
-- imply
  Function.Injective (pos (ons_liftDir v)) := by
-- proof
  apply StatMech.Onsager.ons_liftDir_pos_injective v hvalid hsite

/--
[ons_liftDir_reduce_pos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_liftDir_reduce_pos_injective_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {i j : Fin n}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k => (v k).1))
  (hij : ons_reduceSite L (pos (ons_liftDir v) i) = ons_reduceSite L (pos (ons_liftDir v) j)) :
-- imply
  i = j := by
-- proof
  apply StatMech.Onsager.ons_liftDir_reduce_pos_injective v hvalid hsite hij

/--
[ons_liftDir_no_period_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_liftDir_no_period_translate_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {i j : Fin n}
  {a b : ℤ}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k => (v k).1))
  (hij : pos (ons_liftDir v) i = pos (ons_liftDir v) j + ((L : ℤ) * a, (L : ℤ) * b)) :
-- imply
  i = j ∧ a = 0 ∧ b = 0 := by
-- proof
  apply StatMech.Onsager.ons_liftDir_no_period_translate v hvalid hsite hij

/--
[ons_liftDir_nonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_liftDir_nonUturn_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L}
-- given
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2) :
-- imply
  ∀ k, ons_liftDir v (k + 1) ≠ ons_liftDir v k + 2 := by
-- proof
  apply StatMech.Onsager.ons_liftDir_nonUturn v hnu

/--
[ons_liftDir_turnProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_liftDir_turnProduct_eq
  {L n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {v : Fin n → ons_Dart L} :
-- imply
  (∏ k, ons_turnW omega (v (k + 1)).2 (v k).2) = ∏ k, ons_turnW omega (ons_liftDir v k) (ons_liftDir v (k + 1)) := by
-- proof
  apply StatMech.Onsager.ons_liftDir_turnProduct omega v

/--
[ons_contractible_turnProduct_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_contractible_turnProduct_eq_neg_one_eq
  {L n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {v : Fin n → ons_Dart L}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k => (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hx : ∑ k, ons_dirExponentX (v k).2 = 0)
  (hy : ∑ k, ons_dirExponentY (v k).2 = 0)
  (hn : 3 ≤ n) :
-- imply
  ∏ k, ons_turnW omega (v (k + 1)).2 (v k).2 = -1 := by
-- proof
  apply StatMech.Onsager.ons_contractible_turnProduct_eq_neg_one omega homega hI v hvalid hsite hnu hx hy hn

/--
[ons_contractible_loopWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_contractible_loopWeight_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x omega : ℂ}
  {v : Fin n → ons_Dart L}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k => (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hx : ∑ k, ons_dirExponentX (v k).2 = 0)
  (hy : ∑ k, ons_dirExponentY (v k).2 = 0)
  (hn : 3 ≤ n) :
-- imply
  ons_loopWeight (ons_KWmat L x omega) v = -x ^ n := by
-- proof
  apply StatMech.Onsager.ons_contractible_loopWeight x omega homega hI v hvalid hsite hnu hx hy hn

/--
[ons_contractible_loopWeight_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusContractibleLoop.lean)
-/
@[path]
private lemma ons_contractible_loopWeight_phase_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x omega u w : ℂ}
  {v : Fin n → ons_Dart L}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hu : u ≠ 0)
  (hw : w ≠ 0)
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k => (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hx : ∑ k, ons_dirExponentX (v k).2 = 0)
  (hy : ∑ k, ons_dirExponentY (v k).2 = 0)
  (hn : 3 ≤ n) :
-- imply
  ons_loopWeight (ons_KWmatPhase L x omega u w) v = -x ^ n := by
-- proof
  apply StatMech.Onsager.ons_contractible_loopWeight_phase x omega u w homega hI hu hw v hvalid hsite hnu hx hy hn


-- created on 2026-10-23
