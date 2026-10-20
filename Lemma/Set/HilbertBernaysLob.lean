import Mathlib
import sympy.Basic
import sympy.atlas.Logic.HilbertBernaysLob
open MetaMathlibExt


/--
[hilbert_bernays_lob_second_incompleteness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/HilbertBernaysLob.lean)
-/
@[path]
private lemma hilbert_bernays_lob_second_incompleteness_eq
  :
-- imply
  ∀ (Sentence : Type)
    (Proves : (Sentence → Prop) → Sentence → Prop) (T : Sentence → Prop)
    (Con falseStmt : Sentence) (neg Prov : Sentence → Sentence)
    (imp : Sentence → Sentence → Sentence) (BaseTheory : Sentence → Prop),
    (∀ s, Proves BaseTheory s → Proves T s) →
    (∀ (U : Sentence → Prop) (a b : Sentence),
    Proves U (imp a b) → Proves U a → Proves U b) →
    (∀ (U : Sentence → Prop) (a b : Sentence), Proves U (imp a (imp b a))) →
    (∀ (U : Sentence → Prop) (a b c : Sentence),
    Proves U (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))) →
    (∀ s, neg s = imp s falseStmt) →
    (∃ G, Proves BaseTheory (imp G (neg (Prov G))) ∧
    Proves BaseTheory (imp (neg (Prov G)) G)) →
    (∀ s, Proves T s → Proves T (Prov s)) →
    (∀ a b, Proves T (imp (Prov (imp a b)) (imp (Prov a) (Prov b)))) →
    (∀ s, Proves T (imp (Prov s) (Prov (Prov s)))) →
    (Con = neg (Prov falseStmt)) →
    ¬ Proves T falseStmt →
    ¬ Proves T Con := by
-- proof
  apply MetaMathlibExt.hilbert_bernays_lob_second_incompleteness


-- created on 2026-10-20
