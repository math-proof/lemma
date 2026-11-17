-- Carved from Lemma/Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean: instance decls only.
import Mathlib
import Class.NumberField_Extension

open NumberField TensorProduct

open scoped TensorProduct

namespace FLT.InfiniteAdeleBaseChange

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

variable {K L}


variable (K L)

variable {K L}

section SelfExtension

variable (K)

instance uniqueSelfExtension (v : InfinitePlace K) : Unique (v.Extension K) where
  default := ⟨v, rfl⟩
  uniq w := Subtype.ext w.property

end SelfExtension


end

end FLT.InfiniteAdeleBaseChange
