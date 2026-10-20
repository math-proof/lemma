import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Words.TernaryAbelianCubeFreeLowerBound
open MetaMathlibExt


/--
[abelianCubeFree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/TernaryAbelianCubeFreeLowerBound.lean)
-/
@[path]
private lemma abelianCubeFree_eq
  :
-- imply
  Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) / 24))
    (fun n : ℕ => ((Set.ncard {w : List (Fin 3) | w.length = n ∧
    ¬ ∃ p x y z s : List (Fin 3), w = p ++ x ++ y ++ z ++ s ∧
    x ≠ [] ∧ y ≠ [] ∧ z ≠ [] ∧
    ∀ a : Fin 3, x.count a = y.count a ∧ y.count a = z.count a}) : ℝ)) := by
-- proof
  apply MetaMathlibExt.abelianCubeFree


-- created on 2026-10-20
