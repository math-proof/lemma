import Mathlib
import sympy.Basic
import sympy.atlas.GameTheory.SpragueGrundy
open MetaMathlibExt.SpragueGrundy


/--
[wfRel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean)
-/
@[path]
private lemma wfRel_eq
  {G : ImpartialGame} :
-- imply
  WellFounded (fun a b => a ∈ G.moves b) := by
-- proof
  apply MetaMathlibExt.SpragueGrundy.wfRel G

/--
[isP_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean)
-/
@[path]
private lemma isP_iff_eq
  {G : ImpartialGame}
  {p : G.Pos} :
-- imply
  IsP G p ↔ ∀ q (_ : q ∈ G.moves p), ¬ IsP G q := by
-- proof
  apply MetaMathlibExt.SpragueGrundy.isP_iff G p

/--
[sprague_grundy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean)
-/
@[path]
private lemma sprague_grundy_eq
  {G : ImpartialGame} :
-- imply
  ∃ n : ℕ, Equiv G (nimHeap n) := by
-- proof
  apply MetaMathlibExt.SpragueGrundy.sprague_grundy G


-- created on 2026-10-20
