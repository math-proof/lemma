module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.List.IsReducedDrop.of.IsReduced
public import Theorem.List.Any_And_IsReduced_EraseIdx.of.LtLengthMulWordProdSimple_Length_WordProd.IsReduced.SignChangeExchangeHyp
public import Theorem.Nat.SatisfiesDeletionCondition.of.SignChangeExchangeHyp
public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.StrongExchangeBridge
public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionProof

public section

open CoxeterGroup CoxeterExchangeGenuine StrongExchangeBridge


namespace CoxeterExchange

/--
[exchange_descent_eraseIdx_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/UnconditionalExchange.lean)
-/
@[path]
public theorem exchange_descent_eraseIdx_unconditional
  [Group W]
  [DecidableEq B]
  [Fintype B]
  {word : List B}
  {s : B}
-- given
  (hred : cs.IsReduced word)
  (hdesc : cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word)) :
-- imply
  ∃ i : Fin word.length, cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s ∧ cs.IsReduced (word.eraseIdx i) :=
-- proof
  exchange_descent_eraseIdx
    (CoxeterSignChangeExchangeFinal.signChangeExchangeHyp_unconditional M cs)
    word s hred hdesc

end CoxeterExchange

/--
[exchange_condition_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/UnconditionalExchange.lean)
-/
@[path]
public theorem exchange_condition_unconditional
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W} :
-- imply
  SatisfiesExchangeCondition M cs :=
-- proof
  exchange_condition_from_neg_of_descent M cs
    (CoxeterSignChangeExchangeFinal.signChangeExchangeHyp_unconditional M cs)


namespace CoxeterExchange

/--
[deletion_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/UnconditionalExchange.lean)
-/
@[path]
public theorem deletion_unconditional
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W} :
-- imply
  SatisfiesDeletionCondition M cs :=
-- proof
  deletion_of_exchange cs (exchange_condition_unconditional M cs)

end CoxeterExchange

namespace CoxeterExchange

/--
[corollary_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/UnconditionalExchange.lean)
-/
@[path]
public theorem corollary_unconditional
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W} :
-- imply
  ExchangeCorollary M cs :=
-- proof
  corollary_of_exchange cs (exchange_condition_unconditional M cs)

end CoxeterExchange

namespace CoxeterExchange

/--
[all_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/UnconditionalExchange.lean)
-/
@[path]
public theorem all_unconditional
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W} :
-- imply
  SatisfiesExchangeCondition M cs ∧ SatisfiesDeletionCondition M cs ∧ ExchangeCorollary M cs :=
-- proof
  let hex := exchange_condition_unconditional M cs
  ⟨hex, deletion_of_exchange cs hex, corollary_of_exchange cs hex⟩

end CoxeterExchange

namespace CoxeterExchange

/--
[exchange_implies_deletion_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/UnconditionalExchange.lean)
-/
@[path]
public theorem exchange_implies_deletion_unconditional
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W} :
-- imply
  SatisfiesDeletionCondition M cs :=
-- proof
  exchange_implies_deletion cs
    (CoxeterSignChangeExchangeFinal.signChangeExchangeHyp_unconditional M cs)

end CoxeterExchange

namespace CoxeterExchange

/--
[exchange_implies_corollary_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/UnconditionalExchange.lean)
-/
@[path]
public theorem exchange_implies_corollary_unconditional
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W} :
-- imply
  ExchangeCorollary M cs :=
-- proof
  exchange_implies_corollary cs
    (CoxeterSignChangeExchangeFinal.signChangeExchangeHyp_unconditional M cs)

end CoxeterExchange

namespace CoxeterExchange

/--
[exchange_implies_both_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/UnconditionalExchange.lean)
-/
@[path]
public theorem exchange_implies_both_unconditional
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W} :
-- imply
  SatisfiesDeletionCondition M cs ∧ ExchangeCorollary M cs :=
-- proof
  exchange_implies_both cs
    (CoxeterSignChangeExchangeFinal.signChangeExchangeHyp_unconditional M cs)
end CoxeterExchange
namespace StrongExchangeBridge
variable {W : Type*} [Group W] {B : Type*} [DecidableEq B] [Fintype B]
  {M : CoxeterMatrix B} {cs : CoxeterSystem M W}


namespace StrongExchangeBridge

/--
[exists_reduced_ending_in_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/UnconditionalExchange.lean)
-/
@[path]
public theorem exists_reduced_ending_in_unconditional
  [Group W]
  [DecidableEq B]
  [Fintype B]
  {word : List B}
  {s : B}
-- given
  (hred : cs.IsReduced word)
  (hdesc : cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word)) :
-- imply
  ∃ (prefix_word : List B), cs.IsReduced (prefix_word ++ [s]) ∧ cs.wordProd (prefix_word ++ [s]) = cs.wordProd word ∧ prefix_word.length + 1 = word.length :=
-- proof
  exists_reduced_ending_in
    (CoxeterSignChangeExchangeFinal.signChangeExchangeHyp_unconditional M cs)
    word s hred hdesc

end StrongExchangeBridge


-- created on 2026-10-23
