import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.PermCycleQuotientWeightSum
open Equiv Finset StatMech StatMech.FrontierD


/--
[permCycleClassWeightSum_eq_of_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermCycleQuotientWeightSum.lean)
-/
@[path]
private lemma permCycleClassWeightSum_eq_of_sameCycle_eq
  [Fintype D]
  [DecidableEq D]
  [AddCommMonoid A]
  {sigma : Perm D}
  {d e : D}
  {f : D → A}
-- given
  (hde : sigma.SameCycle d e) :
-- imply
  permCycleClassWeightSum sigma d f = permCycleClassWeightSum sigma e f := by
-- proof
  apply StatMech.FrontierD.permCycleClassWeightSum_eq_of_sameCycle sigma d e f hde

/--
[permCycleClassWeightSum_filter_of_sameCycle_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermCycleQuotientWeightSum.lean)
-/
@[path]
private lemma permCycleClassWeightSum_filter_of_sameCycle_invariant_eq
  [Fintype D]
  [DecidableEq D]
  [AddCommMonoid A]
  {sigma : Perm D}
  [DecidablePred p]
  {f : D → A}
  {d : D}
-- given
  (p : D → Prop)
  (hinv : ∀ d e, sigma.SameCycle d e → (p d ↔ p e)) :
-- imply
  permCycleClassWeightSum sigma d (fun e => if p e then f e else 0) = if p d then permCycleClassWeightSum sigma d f else 0 := by
-- proof
  apply StatMech.FrontierD.permCycleClassWeightSum_filter_of_sameCycle_invariant sigma p f hinv d

/--
[permCycleQuotientWeightSum_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermCycleQuotientWeightSum.lean)
-/
@[path]
private lemma permCycleQuotientWeightSum_mk_eq
  [Fintype D]
  [DecidableEq D]
  [AddCommMonoid A]
  {sigma : Perm D}
  {d : D}
  {f : D → A} :
-- imply
  permCycleQuotientWeightSum sigma (Quot.mk _ d) f = permCycleClassWeightSum sigma d f := by
-- proof
  apply StatMech.FrontierD.permCycleQuotientWeightSum_mk sigma d f

/--
[sum_permCycleQuotientWeightSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermCycleQuotientWeightSum.lean)
-/
@[path]
private lemma sum_permCycleQuotientWeightSum_eq
  [Fintype D]
  [DecidableEq D]
  [AddCommMonoid A]
  {sigma : Perm D}
  {f : D → A} :
-- imply
  (∑ C : StatMech.FrontierA.PermCycleClass sigma, permCycleQuotientWeightSum sigma C f) = ∑ x : D, f x := by
-- proof
  apply StatMech.FrontierD.sum_permCycleQuotientWeightSum sigma f

/--
[eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_fst_mul_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermCycleQuotientWeightSum.lean)
-/
@[path]
private lemma eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_fst_mul_pos_eq
  [Fintype D]
  [DecidableEq D]
  [DecidablePred p]
  {w : D → Int × Int}
  {a b : D}
-- given
  (p : D → Prop)
  (hsum : (∑ d : D, if p d then w d else 0) = 0)
  (hcard : (Finset.univ.filter fun d => p d ∧ w d ≠ 0).card ≤ 2)
  (ha : p a)
  (hb : p b)
  (hsign : 0 < (w a).1 * (w b).1) :
-- imply
  a = b := by
-- proof
  apply StatMech.FrontierD.eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_fst_mul_pos p w hsum hcard ha hb hsign


-- created on 2026-10-23
