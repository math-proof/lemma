/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ULDMotzkinNumberOfRankR.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
/-!
# (u,l,d)-Motzkin numbers of rank r

Provenance: concept `jis_sem_cc3b9e9ca9863189c52ced84`,
source `jis_source_ed70e97a9239ad812ad2e1c8`
(`schork3.tex`, lines 259-275, statement `jis_a4c8498023ac94f370aead45`).
Boundary evidence only: statement `jis_6323169e4d744a20966ea9c4`.
-/


namespace MetaMathlibExt

namespace ULDMotzkin

/-- Admissible steps of rank `r`: up-steps `U_j` with `u j` colors,
level-steps with `l` colors, down-steps `D_j` with `d j` colors.
Colors are intrinsic (`Fin (u j)`, `Fin l`, `Fin (d j)`), so a zero
count yields no steps of that color. Jump sizes use `j.val + 1`, hence
never zero. Concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `admissible_steps`,
statement `jis_a4c8498023ac94f370aead45`. -/
abbrev ULDMotzkinStep (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ) : Type :=
  (Σ _j : Fin r, Fin (u _j)) ⊕ Fin l ⊕ (Σ _j : Fin r, Fin (d _j))

end ULDMotzkin
end MetaMathlibExt
