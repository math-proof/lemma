/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ULDMotzkinNumberOfRankR.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Instance.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR
/-!
# (u,l,d)-Motzkin numbers of rank r

Provenance: concept `jis_sem_cc3b9e9ca9863189c52ced84`,
source `jis_source_ed70e97a9239ad812ad2e1c8`
(`schork3.tex`, lines 259-275, statement `jis_a4c8498023ac94f370aead45`).
Boundary evidence only: statement `jis_6323169e4d744a20966ea9c4`.
-/


namespace MetaMathlibExt

namespace ULDMotzkin

/-- The `(u,l,d)`-Motzkin number of rank `r` and length `n`: the finite
cardinality of the path type. Requires the source rank hypothesis
`1 ≤ r`. Concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `number`,
statement `jis_a4c8498023ac94f370aead45`. -/
def uldMotzkinNumber (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ)
    (hr : 1 ≤ r) (n : ℕ) : ℕ :=
  Fintype.card (ULDMotzkinPath r u l d hr n)

end ULDMotzkin
end MetaMathlibExt
