module

public import Mathlib

public section

open scoped InnerProductSpace


/--
[exists_orthonormal_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/InnerProductSpaces.lean)
-/
public theorem Fin.Nonempty_OrthonormalBasis_Fin_FinrankVV
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
