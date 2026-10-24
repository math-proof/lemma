import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.TitsTheoremProof
import Lemma.Finset.Any_And_EqImageToFunMorph.of.AdjacentToSimplicialComplex.HasSufficientFoldings
import Lemma.Nat.Any_And_EqAdd1AndEqAdd1.of.Gt.EqAdd_1OrEqAdd1.Eq0
import Lemma.List.Any_And_IsReduced_EraseIdx.of.LtLengthMulWordProdSimple_Length_WordProd.IsReduced
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeDeletion
open TitsTheoremProof CoxeterExchange StrongExchangeBridge
open CoxeterExchange
open StrongExchangeBridge


namespace TitsExchangeFromFoldings

/--
[wordProduct_eq_mul_wordProd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/TitsExchangeFromFoldings.lean)
-/
@[path]
lemma wordProduct_eq_mul_wordProd
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {w : M.Group}
  {word : List B} :
-- imply
  wordProduct M w word = w * M.toCoxeterSystem.wordProd word := by
-- proof
  induction word generalizing w with
  | nil =>
    simp only [wordProduct, CoxeterSystem.wordProd_nil, mul_one]
  | cons i rest ih =>
    simp only [wordProduct, CoxeterSystem.wordProd_cons]
    rw [ih]
    group

end TitsExchangeFromFoldings

namespace TitsExchangeFromFoldings

/--
[wordProduct_one_eq_wordProd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/TitsExchangeFromFoldings.lean)
-/
@[path]
lemma wordProduct_one_eq_wordProd
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B} :
-- imply
  wordProduct M 1 word = M.toCoxeterSystem.wordProd word := by
-- proof
  rw [wordProduct_eq_mul_wordProd, one_mul]

end TitsExchangeFromFoldings

namespace TitsExchangeFromFoldings

/--
[typed_gallery_deletion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/TitsExchangeFromFoldings.lean)
-/
@[path]
lemma typed_gallery_deletion
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
-- given
  (hlong : word.length > M.toCoxeterSystem.length (M.toCoxeterSystem.wordProd word)) :
-- imply
  ∃ (i j : Fin word.length), i < j ∧ M.toCoxeterSystem.wordProd ((word.eraseIdx j).eraseIdx i) = M.toCoxeterSystem.wordProd word :=
-- proof
  deletion_unconditional M.toCoxeterSystem word hlong

end TitsExchangeFromFoldings

namespace TitsExchangeFromFoldings

/--
[exchange_condition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/TitsExchangeFromFoldings.lean)
-/
@[path]
lemma exchange_condition
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  SatisfiesExchangeCondition M M.toCoxeterSystem :=
-- proof
  exchange_condition_unconditional M M.toCoxeterSystem

end TitsExchangeFromFoldings


-- created on 2026-10-23
