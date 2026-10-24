/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/KneserLovasz.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.KneserLovasz
import Lemma.Finset.SimpleGraph.KneserLovasz


open MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

example (n k : ℕ) (x y : KneserVertex n k) :
    (kneserGraph n k).Adj x y ↔ Disjoint x.val y.val ∧ x ≠ y :=
  kneserGraph_adj_iff n k x y

example : (kneserGraph 2 1).Adj ⟨{0}, by simp⟩ ⟨{1}, by simp⟩ := by
  rw [kneserGraph_adj_iff]
  decide

example (n k : ℕ) (x : KneserVertex n k) : ¬(kneserGraph n k).Adj x x := by
  rw [kneserGraph_adj_iff]
  simp

example : ¬(kneserGraph 4 2).Adj ⟨{0, 1}, by simp⟩ ⟨{1, 2}, by simp⟩ := by
  rw [kneserGraph_adj_iff]
  decide

example : (kneserGraph 5 2).chromaticNumber = 3 := by
  have h := kneser_lovasz (n := 5) (k := 2) (by omega) (by omega)
  rw [h]
  decide
