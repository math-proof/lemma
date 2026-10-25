/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean -/


import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Def.Combinatorics.SimpleGraph.EdgeGraceful
import Lemma.SimpleGraph.EdgeGraceful
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.EdgeGraceful.Part3


namespace EdgeGracefulTest

def pathLabel : (SimpleGraph.pathGraph 3).edgeSet ≃ Fin 2 where
  toFun := pathToFun
  invFun := pathInvFun
  left_inv := by
    intro e
    rcases eclass e with rfl | rfl
    · show pathInvFun (pathToFun e01) = e01
      rw [hto01, hinv0]
    · show pathInvFun (pathToFun e12) = e12
      rw [hto12, hinv1]
  right_inv := by
    intro k
    fin_cases k
    · change pathToFun (pathInvFun 0) = 0
      rw [hinv0, hto01]
    · change pathToFun (pathInvFun 1) = 1
      rw [hinv1, hto12]

end EdgeGracefulTest
