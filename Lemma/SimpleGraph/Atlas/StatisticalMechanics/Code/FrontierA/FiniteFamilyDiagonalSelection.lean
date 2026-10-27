import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteFamilyDiagonalSelection
open Filter Topology StatMech StatMech.FrontierA


/--
[exists_diagonal_close_on_finiteFamilies_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteFamilyDiagonalSelection.lean)
-/
@[path]
private lemma exists_diagonal_close_on_finiteFamilies_of_pos_eq
  [DecidableEq α]
  {f : α → Nat → Real}
  {limit : α → Real}
  {family : Nat → Finset α}
  {epsilon : Nat → Real}
-- given
  (hf : ∀ a, Tendsto (f a) atTop (nhds (limit a)))
  (hepsilon : ∀ n, 0 < epsilon n) :
-- imply
  ∃ scale : Nat → Nat, Tendsto scale atTop atTop ∧ ∀ n a, a ∈ family n → := by
-- proof
  apply StatMech.FrontierA.exists_diagonal_close_on_finiteFamilies_of_pos f limit hf family epsilon hepsilon

/--
[exists_diagonal_close_on_finiteFamilies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteFamilyDiagonalSelection.lean)
-/
@[path]
private lemma exists_diagonal_close_on_finiteFamilies_eq
  [DecidableEq α]
  {f : α → Nat → Real}
  {limit : α → Real}
  {family : Nat → Finset α}
-- given
  (hf : ∀ a, Tendsto (f a) atTop (nhds (limit a))) :
-- imply
  ∃ scale : Nat → Nat, Tendsto scale atTop atTop ∧ ∀ n a, a ∈ family n → := by
-- proof
  apply StatMech.FrontierA.exists_diagonal_close_on_finiteFamilies f limit hf family

/--
[exists_diagonal_weightedSum_close_on_finiteFamilies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteFamilyDiagonalSelection.lean)
-/
@[path]
private lemma exists_diagonal_weightedSum_close_on_finiteFamilies_eq
  [DecidableEq α]
  {f : α → Nat → Real}
  {limit : α → Real}
  {family : Nat → Finset α}
  {weight : Nat → α → Real}
  {epsilon : Nat → Real}
-- given
  (hf : ∀ a, Tendsto (f a) atTop (nhds (limit a)))
  (hepsilon : ∀ n, 0 < epsilon n) :
-- imply
  ∃ scale : Nat → Nat, Tendsto scale atTop atTop ∧ ∀ n, abs ((∑ a ∈ family n, weight n a * f a (scale n)) - (∑ a ∈ family n, weight n a * limit a)) < epsilon n := by
-- proof
  apply StatMech.FrontierA.exists_diagonal_weightedSum_close_on_finiteFamilies f limit hf family weight epsilon hepsilon


-- created on 2026-10-23
