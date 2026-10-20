import Mathlib
import sympy.Basic
import sympy.atlas.Probability.BertrandBallot
open MetaMathlibExt


/--
[bertrand_ballot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BertrandBallot.lean)
-/
@[path]
private lemma bertrand_ballot_eq
  :
-- imply
  ∀ (p q : ℕ), 1 ≤ q → q < p →
    (Finset.univ.filter (fun σ : Fin (p + q) → Bool =>
    (Finset.univ.filter (fun i : Fin (p + q) => σ i = true)).card = p ∧
    ∀ k : Fin (p + q),
    (Finset.univ.filter (fun i : Fin (p + q) => i ≤ k ∧ σ i = true)).card >
    (Finset.univ.filter (fun i : Fin (p + q) => i ≤ k ∧ σ i = false)).card)).card
    * (p + q) = (p - q) * (p + q).choose q := by
-- proof
  apply MetaMathlibExt.bertrand_ballot


-- created on 2026-10-20
