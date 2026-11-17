/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/EquilibriousWord.lean -/

module

public import Mathlib.Data.List.Count
public import Def.Combinatorics.Words.EquilibriousWord

@[expose] public section

namespace MetaMathlibExt

/-- Decidability of the equilibrious-word predicate, by decidable equality on
the two `List.count` values. Exposed so `by decide` works across the module
boundary. Provenance: concept `jis_sem_061cc96760fa3a6b576dda00`, source
location `coons6.tex:543-575`. -/
instance decidableIsEquilibriousWord (u : List (Fin 2)) :
    Decidable (IsEquilibriousWord u) := by
  unfold IsEquilibriousWord
  infer_instance

end MetaMathlibExt
