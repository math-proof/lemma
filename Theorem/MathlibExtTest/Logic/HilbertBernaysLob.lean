/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Logic/HilbertBernaysLob.lean -/


import Lemma.Set.HilbertBernaysLob
import Inductive.MathlibExtTest.Logic.HilbertBernaysLob


namespace HilbertBernaysLobTest

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
