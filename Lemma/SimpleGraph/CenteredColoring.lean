import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.CenteredColoring
open SimpleGraph


/--
[isPhiCenter_iff_existsUnique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CenteredColoring.lean)
-/
@[path]
private lemma isPhiCenter_iff_existsUnique_eq
  {G : SimpleGraph V}
  {φ : G.Coloring C}
  {s : Set V}
  {v : V} :
-- imply
  IsPhiCenter φ s v ↔ v ∈ s ∧ ∃! u, u ∈ s ∧ φ u = φ v := by
-- proof
  apply SimpleGraph.isPhiCenter_iff_existsUnique φ s v

/--
[isPhiCenter_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CenteredColoring.lean)
-/
@[path]
private lemma isPhiCenter_singleton_eq
  {G : SimpleGraph V}
  {φ : G.Coloring C}
  {v : V} :
-- imply
  IsPhiCenter φ {v} v := by
-- proof
  apply SimpleGraph.isPhiCenter_singleton φ v

/--
[isCentered_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CenteredColoring.lean)
-/
@[path]
private lemma isCentered_of_injective_eq
  {G : SimpleGraph V}
  {φ : G.Coloring C}
-- given
  (hinj : Function.Injective ⇑φ) :
-- imply
  IsCentered φ := by
-- proof
  apply SimpleGraph.isCentered_of_injective φ hinj

/--
[selfColoring_isCentered](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CenteredColoring.lean)
-/
@[path]
private lemma selfColoring_isCentered_eq
  {G : SimpleGraph V} :
-- imply
  IsCentered (SimpleGraph.selfColoring G) := by
-- proof
  apply SimpleGraph.selfColoring_isCentered G


-- created on 2026-10-20
