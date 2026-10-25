/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ULDMotzkinNumberOfRankR.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Def.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR
/-!
# (u,l,d)-Motzkin numbers of rank r

Provenance: concept `jis_sem_cc3b9e9ca9863189c52ced84`,
source `jis_source_ed70e97a9239ad812ad2e1c8`
(`schork3.tex`, lines 259-275, statement `jis_a4c8498023ac94f370aead45`).
Boundary evidence only: statement `jis_6323169e4d744a20966ea9c4`.
-/


namespace MetaMathlibExt

namespace ULDMotzkin

/-- Decidability of the Motzkin path predicate, by computation over the
finite prefix quantification with decidability over the integers.
Concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `paths`,
statement `jis_a4c8498023ac94f370aead45`. -/
instance isMotzkinPathDecPred (r : ℕ) (u : Fin r → ℕ) (l : ℕ)
    (d : Fin r → ℕ) (hr : 1 ≤ r) (n : ℕ) :
    DecidablePred (IsMotzkinPath r u l d hr n) :=
  fun p => by unfold IsMotzkinPath; infer_instance

/-- Finite type of Motzkin paths, via the decidable subtype. Concept
`jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `number`,
statement `jis_a4c8498023ac94f370aead45`. -/
instance uldMotzkinPathFintype (r : ℕ) (u : Fin r → ℕ) (l : ℕ)
    (d : Fin r → ℕ) (hr : 1 ≤ r) (n : ℕ) :
    Fintype (ULDMotzkinPath r u l d hr n) :=
  Subtype.fintype _

end ULDMotzkin
end MetaMathlibExt
