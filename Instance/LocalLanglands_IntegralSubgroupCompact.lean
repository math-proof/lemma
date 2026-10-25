-- Carved from Lemma/Definitions/Def_LocalLanglands_IntegralSubgroupCompact.lean: instance decls only.
import Mathlib
set_option autoImplicit false

namespace FLT.SpectralSide

instance instCompactSpaceMatrix {m n R : Type*} [TopologicalSpace R] [CompactSpace R] :
    CompactSpace (Matrix m n R) :=
  inferInstanceAs <| CompactSpace (m → n → R)


end FLT.SpectralSide
