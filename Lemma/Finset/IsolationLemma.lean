import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.IsolationLemma
open scoped BigOperators
open MetaMathlibExt


/--
[isolation_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsolationLemma.lean)
-/
@[path]
private lemma isolation_lemma_eq
  {n : ℕ}
  {F : Finset (Finset (Fin n))}
-- given
  (hn : 0 < n)
  (hF : F.Nonempty) :
-- imply
  (((Finset.univ.filter (fun w : Fin n → Fin (2 * n) =>
    (F.filter (fun S => ∀ T ∈ F,
    ∑ i ∈ S, ((w i).val + 1) ≤ ∑ i ∈ T, ((w i).val + 1))).card = 1)).card : ℚ)
    / (Fintype.card (Fin n → Fin (2 * n)) : ℚ)) ≥ 1 / 2 := by
-- proof
  apply MetaMathlibExt.isolation_lemma hn F hF


-- created on 2026-10-20
