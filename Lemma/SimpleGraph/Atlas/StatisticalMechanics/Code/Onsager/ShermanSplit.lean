import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanSplit.Part5
open StatMech StatMech.Onsager


/--
[ons_edgeWeight_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_edgeWeight_nil_eq
  {Λ : Matrix E E ℂ} :
-- imply
  ons_edgeWeight Λ ([] : List E) = 1 := by
-- proof
  apply StatMech.Onsager.ons_edgeWeight_nil Λ

/--
[ons_edgeWeight_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_edgeWeight_singleton_eq
  {Λ : Matrix E E ℂ}
  {a : E} :
-- imply
  ons_edgeWeight Λ [a] = 1 := by
-- proof
  apply StatMech.Onsager.ons_edgeWeight_singleton Λ a

/--
[ons_edgeWeight_cons_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_edgeWeight_cons_cons_eq
  {Λ : Matrix E E ℂ}
  {a b : E}
  {t : List E} :
-- imply
  ons_edgeWeight Λ (a :: b :: t) = Λ a b * ons_edgeWeight Λ (b :: t) := by
-- proof
  apply StatMech.Onsager.ons_edgeWeight_cons_cons Λ a b t

/--
[ons_edgeWeight_append_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_edgeWeight_append_cons_eq
  {Λ : Matrix E E ℂ}
  {u : List E}
  {b : E}
  {v : List E} :
-- imply
  ons_edgeWeight Λ (u ++ b :: v) = ons_edgeWeight Λ (u ++ [b]) * ons_edgeWeight Λ (b :: v) := by
-- proof
  apply StatMech.Onsager.ons_edgeWeight_append_cons Λ u b v

/--
[ons_glue_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_glue_nil_eq
  {e : E} :
-- imply
  ons_glue e [] = [e] := by
-- proof
  apply StatMech.Onsager.ons_glue_nil e

/--
[ons_glue_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_glue_cons_eq
  {e : E}
  {s : List E}
  {ss : List (List E)} :
-- imply
  ons_glue e (s :: ss) = s.dropLast ++ ons_glue e ss := by
-- proof
  apply StatMech.Onsager.ons_glue_cons e s ss

/--
[ons_glue_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_glue_head_eq
  {e : E}
  {ss : List (List E)}
-- given
  (hhead : ∀ s ∈ ss, s.head? = some e) :
-- imply
  ∃ t, ons_glue e ss = e :: t := by
-- proof
  apply StatMech.Onsager.ons_glue_head e ss hhead

/--
[ons_edgeWeight_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_edgeWeight_glue_eq
  {Λ : Matrix E E ℂ}
  {e : E}
  {ss : List (List E)}
-- given
  (hhead : ∀ s ∈ ss, s.head? = some e)
  (hlast : ∀ s ∈ ss, s.getLast? = some e) :
-- imply
  ons_edgeWeight Λ (ons_glue e ss) = (ss.map (ons_edgeWeight Λ)).prod := by
-- proof
  apply StatMech.Onsager.ons_edgeWeight_glue Λ e ss hhead hlast

/--
[ons_glue_firstReturnSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_glue_firstReturnSplit_eq
  [DecidableEq E]
  {e : E}
  {w : List E}
-- given
  (hw : w.getLast? = some e) :
-- imply
  ons_glue e (ons_firstReturnSplit e w) = w := by
-- proof
  apply StatMech.Onsager.ons_glue_firstReturnSplit e w hw

/--
[ons_firstReturnSegment_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_firstReturnSegment_head_eq
  [DecidableEq E]
  {e : E}
  {s : List E}
-- given
  (hs : ons_isFirstReturnSegment e s) :
-- imply
  s.head? = some e := by
-- proof
  apply StatMech.Onsager.ons_firstReturnSegment_head hs

/--
[ons_firstReturnSegment_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_firstReturnSegment_last_eq
  [DecidableEq E]
  {e : E}
  {s : List E}
-- given
  (hs : ons_isFirstReturnSegment e s) :
-- imply
  s.getLast? = some e := by
-- proof
  apply StatMech.Onsager.ons_firstReturnSegment_last hs

/--
[ons_firstReturnSplit_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_firstReturnSplit_glue_eq
  [DecidableEq E]
  {e : E}
  {ss : List (List E)}
-- given
  (hfirst : ∀ s ∈ ss, ons_isFirstReturnSegment e s) :
-- imply
  ons_firstReturnSplit e (ons_glue e ss) = ss ++ [[e]] := by
-- proof
  apply StatMech.Onsager.ons_firstReturnSplit_glue e ss hfirst

/--
[ons_firstReturnSplit_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_firstReturnSplit_closed_eq
  [DecidableEq E]
  {e : E}
  {w : List E}
-- given
  (hhead : w.head? = some e)
  (hlast : w.getLast? = some e) :
-- imply
  ∃ ss : List (List E), ons_firstReturnSplit e w = ss ++ [[e]] ∧ ∀ s ∈ ss, ons_isFirstReturnSegment e s := by
-- proof
  apply StatMech.Onsager.ons_firstReturnSplit_closed e w hhead hlast

/--
[ons_count_ofFn_eq_visitCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_count_ofFn_eq_visitCount_eq
  [DecidableEq E]
  {e : E}
  {n : ℕ}
  {v : Fin n → E} :
-- imply
  (List.ofFn v).count e = Fintype.card {k : Fin n // v k = e} := by
-- proof
  apply StatMech.Onsager.ons_count_ofFn_eq_visitCount e v

/--
[ons_glue_append_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_glue_append_terminal_eq
  [DecidableEq E]
  {e : E}
  {ss : List (List E)} :
-- imply
  ons_glue e (ss ++ [[e]]) = ons_glue e ss := by
-- proof
  apply StatMech.Onsager.ons_glue_append_terminal e ss

/--
[ons_count_glue_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_count_glue_firstReturn_eq
  [DecidableEq E]
  {e : E}
  {ss : List (List E)}
-- given
  (hfirst : ∀ s ∈ ss, ons_isFirstReturnSegment e s) :
-- imply
  (ons_glue e ss).count e = ss.length + 1 := by
-- proof
  apply StatMech.Onsager.ons_count_glue_firstReturn e ss hfirst

/--
[ons_firstReturnFactors_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_firstReturnFactors_spec_eq
  [DecidableEq E]
  {e : E}
  {w : List E}
-- given
  (hhead : w.head? = some e)
  (hlast : w.getLast? = some e) :
-- imply
  ons_firstReturnSplit e w = ons_firstReturnFactors e w ++ [[e]] ∧ (∀ s ∈ ons_firstReturnFactors e w, ons_isFirstReturnSegment e s) ∧ ons_glue e (ons_firstReturnFactors e w) = w := by
-- proof
  apply StatMech.Onsager.ons_firstReturnFactors_spec e w hhead hlast

/--
[ons_edgeWeight_firstReturnSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean)
-/
@[path]
private lemma ons_edgeWeight_firstReturnSplit_eq
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
  {e : E}
  {w : List E} :
-- imply
  ((ons_firstReturnSplit e w).map (ons_edgeWeight Λ)).prod = ons_edgeWeight Λ w := by
-- proof
  apply StatMech.Onsager.ons_edgeWeight_firstReturnSplit Λ e w


-- created on 2026-10-23
