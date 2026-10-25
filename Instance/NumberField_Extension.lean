-- Carved from Lemma/Definitions/Def_NumberField_Extension.lean: instance decls only.
import Mathlib
import Abbrev.NumberField_Extension
import Class.NumberField_Extension

section

noncomputable section


namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] (v : InfinitePlace K) (w : InfinitePlace L)

variable [Algebra K L]


variable (L)


namespace RamifiedExtension

instance : Coe (v.RamifiedExtension L) (v.Extension L) where
  coe w := ⟨w.1, w.2.1⟩

end RamifiedExtension

namespace UnramifiedExtension

instance : Coe (v.UnramifiedExtension L) (v.Extension L) where
  coe w := ⟨w.1, w.comap_eq⟩

end UnramifiedExtension

end NumberField.InfinitePlace
end
end
