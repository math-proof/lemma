import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped InnerProductSpace


/--
[exists_orthonormal_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/InnerProductSpaces.lean)
-/
@[path]
private lemma main
  [RCLike 𝕜]
  [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] :
-- imply
  Nonempty (OrthonormalBasis (Fin (Module.finrank 𝕜 V)) 𝕜 V) :=
-- proof
  ⟨stdOrthonormalBasis 𝕜 V⟩



-- created on 2026-10-23
-- updated on 2026-10-26
