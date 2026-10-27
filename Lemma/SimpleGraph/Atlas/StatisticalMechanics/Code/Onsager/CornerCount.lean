import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.CornerCount.Part3
open StatMech StatMech.Onsager StatMech.Onsager.CornerCount


/--
[bigSquare_cc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean)
-/
@[path]
private lemma bigSquare_cc_eq :
-- imply
  ccCount bigSquare = 0 := by
-- proof
  apply StatMech.Onsager.CornerCount.bigSquare_cc

/--
[bigSquare_rc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean)
-/
@[path]
private lemma bigSquare_rc_eq :
-- imply
  rcCount bigSquare = 0 := by
-- proof
  apply StatMech.Onsager.CornerCount.bigSquare_rc

/--
[bigSquare_simple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean)
-/
@[path]
private lemma bigSquare_simple_eq :
-- imply
  simplePred bigSquare := by
-- proof
  apply StatMech.Onsager.CornerCount.bigSquare_simple

/--
[hbase_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean)
-/
@[path]
private lemma hbase_false_eq :
-- imply
  ¬ (∀ V : List Pt, simplePred V → rcCount V = 0 → ccCount V = 4) := by
-- proof
  apply StatMech.Onsager.CornerCount.hbase_false

/--
[sum_eq_ccrc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean)
-/
@[path]
private lemma sum_eq_ccrc_eq
  {L : List ℤ}
-- given
  (h : ∀ t ∈ L, t = -1 ∨ t = 0 ∨ t = 1) :
-- imply
  L.sum = ((L.countP (fun t => t == 1) : ℕ) : ℤ) - ((L.countP (fun t => t == -1) : ℕ) : ℤ) := by
-- proof
  apply StatMech.Onsager.CornerCount.sum_eq_ccrc L h

/--
[cornerBalanceL_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean)
-/
@[path]
private lemma cornerBalanceL_eq_eq
  {V : List Pt}
-- given
  (h : ∀ t ∈ turnList V, t = -1 ∨ t = 0 ∨ t = 1) :
-- imply
  cornerBalanceL V = ccCount V - rcCount V := by
-- proof
  apply StatMech.Onsager.CornerCount.cornerBalanceL_eq V h

/--
[mem_zipWith_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean)
-/
@[path]
private lemma mem_zipWith_imp_eq
  {f : α → β → γ} :
-- imply
  ∀ (l₁ : List α) (l₂ : List β) (c : γ), c ∈ List.zipWith f l₁ l₂ → ∃ a b, a ∈ l₁ ∧ b ∈ l₂ ∧ c = f a b := by
-- proof
  apply StatMech.Onsager.CornerCount.mem_zipWith_imp f

/--
[turnList_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean)
-/
@[path]
private lemma turnList_eq_eq
  {V : List Pt} :
-- imply
  turnList V = List.zipWith turn (stepList V) ((stepList V).rotate 1) := by
-- proof
  apply StatMech.Onsager.CornerCount.turnList_eq V

/--
[turnList_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean)
-/
@[path]
private lemma turnList_bounded_eq
  {V : List Pt}
-- given
  (hunit : ∀ d ∈ stepList V, StatMech.Onsager.PolygonWalk.isUnitDir d) :
-- imply
  ∀ t ∈ turnList V, t = -1 ∨ t = 0 ∨ t = 1 := by
-- proof
  apply StatMech.Onsager.CornerCount.turnList_bounded V hunit

/--
[cornerBalanceL_eq_of_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean)
-/
@[path]
private lemma cornerBalanceL_eq_of_unit_eq
  {V : List Pt}
-- given
  (hunit : ∀ d ∈ stepList V, StatMech.Onsager.PolygonWalk.isUnitDir d) :
-- imply
  cornerBalanceL V = ccCount V - rcCount V := by
-- proof
  apply StatMech.Onsager.CornerCount.cornerBalanceL_eq_of_unit V hunit

/--
[balanceL_split_of_counts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean)
-/
@[path]
private lemma balanceL_split_of_counts_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (hbV : ∀ t ∈ turnList V, t = -1 ∨ t = 0 ∨ t = 1)
  (hbA : ∀ t ∈ turnList (arc V a b), t = -1 ∨ t = 0 ∨ t = 1)
  (hbC : ∀ t ∈ turnList (coarc V a b), t = -1 ∨ t = 0 ∨ t = 1)
  (hcc : ccCount (arc V a b) + ccCount (coarc V a b) = ccCount V + 3)
  (hrc : rcCount (arc V a b) + rcCount (coarc V a b) = rcCount V - 1) :
-- imply
  cornerBalanceL V = cornerBalanceL (arc V a b) + cornerBalanceL (coarc V a b) - 4 := by
-- proof
  apply StatMech.Onsager.CornerCount.balanceL_split_of_counts V a b hbV hbA hbC hcc hrc


-- created on 2026-10-23
