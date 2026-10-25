import Mathlib

set_option autoImplicit false

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

namespace Extension

variable (L) (v : InfinitePlace K)
  (w : { w : InfinitePlace L // w.comap (algebraMap K L) = v })

class IsLift where
  isExtension' : w.1.embedding.comp (algebraMap K L) = v.embedding

class IsConjugateLift where
  isExtension' : (conjugate w.1.embedding).comp (algebraMap K L) = v.embedding

end Extension

end NumberField.InfinitePlace
