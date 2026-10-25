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

end HilbertBernaysLobTest
