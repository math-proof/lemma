/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Logic/HilbertBernaysLob.lean -/


import Lemma.Set.HilbertBernaysLob

namespace HilbertBernaysLobTest

inductive Formula where
  | atom
  | imp (a b : Formula)

inductive Derives (U : Formula → Prop) : Formula → Prop where
  | assumption {a : Formula} : U a → Derives U a
  | mp {a b : Formula} : Derives U (.imp a b) → Derives U a → Derives U b
  | k (a b : Formula) : Derives U (.imp a (.imp b a))
  | s (a b c : Formula) :
      Derives U (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))

-- The abstract theorem specializes to an ordinary K/S Hilbert derivation relation.
example
    (T BaseTheory : Formula → Prop) (Con falseStmt : Formula)
    (neg Prov : Formula → Formula)
    (hbase : ∀ s, Derives BaseTheory s → Derives T s)
    (hneg : ∀ s, neg s = .imp s falseStmt)
    (hdiag : ∃ G, Derives BaseTheory (.imp G (neg (Prov G))) ∧
      Derives BaseTheory (.imp (neg (Prov G)) G))
    (hd1 : ∀ s, Derives T s → Derives T (Prov s))
    (hd2 : ∀ a b, Derives T (.imp (Prov (.imp a b)) (.imp (Prov a) (Prov b))))
    (hd3 : ∀ s, Derives T (.imp (Prov s) (Prov (Prov s))))
    (hcon : Con = neg (Prov falseStmt))
    (hconsistent : ¬ Derives T falseStmt) :
    ¬ Derives T Con := by
  exact MetaMathlibExt.hilbert_bernays_lob_second_incompleteness
    Formula Derives T Con falseStmt neg Prov Formula.imp BaseTheory hbase
    (fun _ _ _ hab ha => .mp hab ha) (fun _ a b => .k a b)
    (fun _ a b c => .s a b c) hneg hdiag hd1 hd2 hd3 hcon hconsistent

end HilbertBernaysLobTest
