import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexContentHalfBound.Part3
open StatMech StatMech.Universality


/--
[hchb_eq_of_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentHalfBound.lean)
-/
@[path]
private lemma hchb_eq_of_mem_iff_eq
  {s t : HexHWContentHalf}
-- given
  (hmem : forall b : HexBridge, b ∈ s.1 ↔ b ∈ t.1) :
-- imply
  s = t := by
-- proof
  apply StatMech.Universality.hchb_eq_of_mem_iff s t hmem

/--
[hchb_find_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentHalfBound.lean)
-/
@[path]
private lemma hchb_find_eq_some_iff_eq
  {s : HexHWContentHalf}
  {T : ℕ}
  {b : HexBridge} :
-- imply
  hchb_find s T = some b ↔ b ∈ s.1 ∧ b.width = T := by
-- proof
  apply StatMech.Universality.hchb_find_eq_some_iff s T b

/--
[hchb_encode_mem_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentHalfBound.lean)
-/
@[path]
private lemma hchb_encode_mem_pi_eq
  {S : Finset HexHWContentHalf}
  {s : HexHWContentHalf}
-- given
  (hs : s ∈ S) :
-- imply
  (fun T (_hT : T ∈ hchb_active S) => hchb_find s T) ∈ (hchb_active S).pi (hchb_choices S) := by
-- proof
  apply StatMech.Universality.hchb_encode_mem_pi S s hs

/--
[hchb_encode_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentHalfBound.lean)
-/
@[path]
private lemma hchb_encode_injOn_eq
  {S : Finset HexHWContentHalf} :
-- imply
  Set.InjOn (fun s => fun T (_hT : T ∈ hchb_active S) => hchb_find s T) (S : Set HexHWContentHalf) := by
-- proof
  apply StatMech.Universality.hchb_encode_injOn S

/--
[hchb_halfWeight_eq_widthProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentHalfBound.lean)
-/
@[path]
private lemma hchb_halfWeight_eq_widthProd_eq
  {x : ℝ}
  {s : HexHWContentHalf} :
-- imply
  hhc_halfWeight x s = ∏ T ∈ hhc_widths s, hchb_choiceWeight x T (hchb_find s T) := by
-- proof
  apply StatMech.Universality.hchb_halfWeight_eq_widthProd x s

/--
[hchb_halfWeight_eq_activeProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentHalfBound.lean)
-/
@[path]
private lemma hchb_halfWeight_eq_activeProd_eq
  {S : Finset HexHWContentHalf}
  {x : ℝ}
  {s : HexHWContentHalf}
-- given
  (hs : s ∈ S) :
-- imply
  hhc_halfWeight x s = ∏ T ∈ hchb_active S, hchb_choiceWeight x T (hchb_find s T) := by
-- proof
  apply StatMech.Universality.hchb_halfWeight_eq_activeProd S x s hs

/--
[hchb_sum_choices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentHalfBound.lean)
-/
@[path]
private lemma hchb_sum_choices_eq
  {S : Finset HexHWContentHalf}
  {x : ℝ}
  {T : ℕ} :
-- imply
  ∑ o ∈ hchb_choices S T, hchb_choiceWeight x T o = 1 + hchb_bridgeMass S x T := by
-- proof
  apply StatMech.Universality.hchb_sum_choices S x T

/--
[hchb_sum_halfWeight_le_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentHalfBound.lean)
-/
@[path]
private lemma hchb_sum_halfWeight_le_prod_eq
  {S : Finset HexHWContentHalf}
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  ∑ s ∈ S, hhc_halfWeight x s ≤ ∏ T ∈ hchb_active S, (1 + hchb_bridgeMass S x T) := by
-- proof
  apply StatMech.Universality.hchb_sum_halfWeight_le_prod S hx

/--
[hchb_sum_halfWeight_le_tprod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentHalfBound.lean)
-/
@[path]
private lemma hchb_sum_halfWeight_le_tprod_eq
  {S : Finset HexHWContentHalf}
  {x : ℝ}
  {ups : ℕ → ℝ}
-- given
  (hx : 0 ≤ x)
  (hups : ∀ T, 0 ≤ ups T)
  (hmul : Multipliable (fun T => 1 + ups T))
  (hmass : ∀ T, hchb_bridgeMass S x T ≤ ups T) :
-- imply
  ∑ s ∈ S, hhc_halfWeight x s ≤ ∏' T, (1 + ups T) := by
-- proof
  apply StatMech.Universality.hchb_sum_halfWeight_le_tprod S hx ups hups hmul hmass


-- created on 2026-10-23
