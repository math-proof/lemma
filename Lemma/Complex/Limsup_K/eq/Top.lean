import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_987
open Filter Complex Finset


/--
[Erdos_987](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_987.lean)
-/
@[path]
private lemma main
  {z: ℕ → Circle} :
-- imply
  atTop.limsup (fun k:ℕ ↦ atTop.limsup (fun n:ℕ ↦ (‖∑ j ∈ range n, ((z j)^k:ℂ)‖:EReal) )) = ⊤ :=
-- proof
  Erdos_987 z


-- created on 2026-10-22
