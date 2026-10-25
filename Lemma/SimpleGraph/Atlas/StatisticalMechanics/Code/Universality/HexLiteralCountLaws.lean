import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
open StatMech StatMech.Universality


/--
[hlc_sawCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_sawCount_zero_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hlc_sawCount a h0 0 = 1 := by
-- proof
  apply StatMech.Universality.hlc_sawCount_zero a h0

/--
[hlc_sawCountR_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_sawCountR_zero_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hlc_sawCountR a h0 0 = 1 := by
-- proof
  apply StatMech.Universality.hlc_sawCountR_zero a h0

/--
[hlc_length_zigzagTurnsAux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_length_zigzagTurnsAux_eq
  {phase : Bool}
  {n : ℕ} :
-- imply
  (hlc_zigzagTurnsAux phase n).length = n := by
-- proof
  apply StatMech.Universality.hlc_length_zigzagTurnsAux phase n

/--
[hlc_length_zigzagTurns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_length_zigzagTurns_eq
  {n : ℕ} :
-- imply
  (hlc_zigzagTurns n).length = n := by
-- proof
  apply StatMech.Universality.hlc_length_zigzagTurns n

/--
[hlc_zigzagTurns_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_zigzagTurns_legal_eq
  {phase : Bool}
  {n : ℕ} :
-- imply
  ∀ t ∈ hlc_zigzagTurnsAux phase n, t = 1 ∨ t = -1 := by
-- proof
  apply StatMech.Universality.hlc_zigzagTurns_legal phase n

/--
[hlc_halfStep_zero_re_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_halfStep_zero_re_pos_eq :
-- imply
  0 < (halfStep 0).re := by
-- proof
  apply StatMech.Universality.hlc_halfStep_zero_re_pos

/--
[hlc_halfStep_neg_one_re_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_halfStep_neg_one_re_pos_eq :
-- imply
  0 < (halfStep (-1)).re := by
-- proof
  apply StatMech.Universality.hlc_halfStep_neg_one_re_pos

/--
[hlc_zigzag_vertices_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_zigzag_vertices_chain_eq
  {n : ℕ} :
-- imply
  (∀ m : ℂ, List.IsChain (fun z w : ℂ => z.re < w.re) (verticesAux m 0 (hlc_zigzagTurnsAux false n))) ∧ (∀ m : ℂ, List.IsChain (fun z w : ℂ => z.re < w.re) (verticesAux m (-1) (hlc_zigzagTurnsAux true n))) := by
-- proof
  apply StatMech.Universality.hlc_zigzag_vertices_chain n

/--
[hlc_zigzag_isLegalSAW_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_zigzag_isLegalSAW_zero_eq
  {a : ℂ}
  {n : ℕ} :
-- imply
  (ofTurns a 0 (hlc_zigzagTurns n)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlc_zigzag_isLegalSAW_zero a n

/--
[hlc_zigzag_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_zigzag_isLegalSAW_eq
  {a : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 (hlc_zigzagTurns n)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlc_zigzag_isLegalSAW a h0 n

/--
[hlc_one_le_sawCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_one_le_sawCount_eq
  {a : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  1 ≤ hlc_sawCount a h0 n := by
-- proof
  apply StatMech.Universality.hlc_one_le_sawCount a h0 n

/--
[hlc_one_le_sawCountR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_one_le_sawCountR_eq
  {a : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  1 ≤ hlc_sawCountR a h0 n := by
-- proof
  apply StatMech.Universality.hlc_one_le_sawCountR a h0 n

/--
[hlc_card_sawFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_card_sawFinset_eq
  {a : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  (hlc_sawFinset a h0 n).card = hlc_sawCount a h0 n := by
-- proof
  apply StatMech.Universality.hlc_card_sawFinset a h0 n

/--
[hlc_mem_sawFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_mem_sawFinset_eq
  {a : ℂ}
  {n : ℕ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  ts ∈ hlc_sawFinset a h0 n ↔ (ofTurns a h0 ts).IsLegalSAW ∧ ts.length = n := by
-- proof
  apply StatMech.Universality.hlc_mem_sawFinset a h0 n ts

/--
[hlc_split_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_split_mem_eq
  {a : ℂ}
  {m n : ℕ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hts : ts ∈ hlc_sawFinset a h0 (m + n)) :
-- imply
  (ts.take m, ts.drop m) ∈ hlc_sawFinset a h0 m ×ˢ hlc_sawFinset a h0 n := by
-- proof
  apply StatMech.Universality.hlc_split_mem a h0 m n hts

/--
[hlc_split_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_split_injective_eq
  {m : ℕ} :
-- imply
  Function.Injective (fun ts : List ℤ => (ts.take m, ts.drop m)) := by
-- proof
  apply StatMech.Universality.hlc_split_injective m

/--
[hlc_sawCount_submult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_sawCount_submult_eq
  {a : ℂ}
  {m n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hlc_sawCount a h0 (m + n) ≤ hlc_sawCount a h0 m * hlc_sawCount a h0 n := by
-- proof
  apply StatMech.Universality.hlc_sawCount_submult a h0 m n

/--
[hlc_sawCountR_submultiplicative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_sawCountR_submultiplicative_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  Submultiplicative (hlc_sawCountR a h0) := by
-- proof
  apply StatMech.Universality.hlc_sawCountR_submultiplicative a h0

/--
[hlc_sawFinset_rebase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_sawFinset_rebase_eq
  {a a' : ℂ}
  {n : ℕ}
-- given
  (h0 h0' : ℤ) :
-- imply
  hlc_sawFinset a' h0' n = hlc_sawFinset a h0 n := by
-- proof
  apply StatMech.Universality.hlc_sawFinset_rebase a a' h0 h0' n

/--
[hlc_sawCount_rebase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_sawCount_rebase_eq
  {a a' : ℂ}
  {n : ℕ}
-- given
  (h0 h0' : ℤ) :
-- imply
  hlc_sawCount a' h0' n = hlc_sawCount a h0 n := by
-- proof
  apply StatMech.Universality.hlc_sawCount_rebase a a' h0 h0' n

/--
[hlc_sawCountR_rebase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean)
-/
@[path]
private lemma hlc_sawCountR_rebase_eq
  {a a' : ℂ}
  {n : ℕ}
-- given
  (h0 h0' : ℤ) :
-- imply
  hlc_sawCountR a' h0' n = hlc_sawCountR a h0 n := by
-- proof
  apply StatMech.Universality.hlc_sawCountR_rebase a a' h0 h0' n


-- created on 2026-10-23
