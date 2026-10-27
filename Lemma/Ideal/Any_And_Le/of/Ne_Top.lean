import Mathlib
import Initialize.Tactic.Attr.Basic


namespace AlgebraicIntegers

/--
[ideal_le_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/AlgebraicIntegers.lean)
-/
@[path]
lemma ideal_le_maximal
  [CommRing R]
  [Nontrivial R]
  [IsNoetherianRing R]
  {I : Ideal R}
-- given
  (hI : I ≠ ⊤) :
-- imply
  ∃ M : Ideal R, M.IsMaximal ∧ I ≤ M :=
-- proof
  Ideal.exists_le_maximal I hI

end AlgebraicIntegers


-- created on 2026-10-23
