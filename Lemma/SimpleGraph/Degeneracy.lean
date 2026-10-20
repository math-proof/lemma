import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Degeneracy
open SimpleGraph


/--
[IsDegenerateOn.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Degeneracy.lean)
-/
@[path]
private lemma IsDegenerateOn_mono_eq
  [Finite V]
  {G : SimpleGraph V}
  {U T : Set V}
  {k l : ℕ}
-- given
  (h : G.IsDegenerateOn U k)
  (hkl : k ≤ l) :
-- imply
  G.IsDegenerateOn U l := by
-- proof
  apply SimpleGraph.IsDegenerateOn.mono h hkl

/--
[IsDegenerateOn.of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Degeneracy.lean)
-/
@[path]
private lemma IsDegenerateOn_of_subset_eq
  [Finite V]
  {G : SimpleGraph V}
  {U T : Set V}
  {k l : ℕ}
-- given
  (h : G.IsDegenerateOn U k)
  (hTU : T ⊆ U) :
-- imply
  G.IsDegenerateOn T k := by
-- proof
  apply SimpleGraph.IsDegenerateOn.of_subset h hTU

/--
[IsDegenerate.isDegenerateOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Degeneracy.lean)
-/
@[path]
private lemma IsDegenerate_isDegenerateOn_eq
  [Finite V]
  {G : SimpleGraph V}
  {U T : Set V}
  {k l : ℕ}
  {U : Set V}
-- given
  (h : G.IsDegenerate k) :
-- imply
  G.IsDegenerateOn U k := by
-- proof
  apply SimpleGraph.IsDegenerate.isDegenerateOn h U


-- created on 2026-10-20
