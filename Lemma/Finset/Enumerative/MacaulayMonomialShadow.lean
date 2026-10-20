import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MacaulayMonomialShadow
open BigOperators
open MetaMathlibExt


/--
[macaulay_multiset_shadow_minimal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean)
-/
@[path]
private lemma macaulay_multiset_shadow_minimal_eq
  {k : ℕ}
  {A : Finset (ℕ →₀ ℕ)}
  {digits : Fin (k + 1) → ℕ}
-- given
  (hdegree : ∀ a ∈ A, a.sum (fun _ e => e) = k + 1)
  (hstrict : StrictMono digits)
  (hcard : A.card = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
-- imply
  (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤
    (A.biUnion fun a => a.support.image fun i => a.update i (a i - 1)).card := by
-- proof
  apply MetaMathlibExt.macaulay_multiset_shadow_minimal k A digits hdegree hstrict hcard


-- created on 2026-10-20
