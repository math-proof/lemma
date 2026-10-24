/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MacaulayMonomialShadow.lean -/


import sympy.atlas.Combinatorics.Enumerative.MacaulayMonomialShadow
import Lemma.Finset.Enumerative.MacaulayMonomialShadow

open BigOperators
open MetaMathlibExt

-- The public theorem applies directly to a degree-two family.
example (A : Finset (ℕ →₀ ℕ)) (digits : Fin 2 → ℕ)
    (hdegree : ∀ a ∈ A, a.sum (fun _ e => e) = 2)
    (hstrict : StrictMono digits)
    (hcard : A.card = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
    (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤
      (A.biUnion fun a => a.support.image fun i => a.update i (a i - 1)).card := by
  simpa using macaulay_multiset_shadow_minimal 1 A digits hdegree hstrict hcard
