import Mathlib

section

noncomputable section

namespace NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
  (f : K →+* ℂ) (g : L →+* ℂ)

abbrev IsExtension := g.comp (algebraMap K L) = f

variable {f g} in

abbrev IsMixedExtension :=
  IsExtension f g ∧ ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g


namespace IsMixedExtension


end IsMixedExtension

abbrev IsUnmixedExtension := IsExtension f g ∧ ¬IsMixedExtension f g

variable {f g} in


end NumberField.ComplexEmbedding

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] (v : InfinitePlace K) (w : InfinitePlace L)

variable [Algebra K L]

variable (L) in

abbrev Extension (v : InfinitePlace K) := { w : InfinitePlace L // w.comap (algebraMap K L) = v }

variable (K) in

abbrev toExtension : (w.comap (algebraMap K L)).Extension L := ⟨w, rfl⟩


namespace Extension

variable {v : InfinitePlace K} (w : v.Extension L)


end Extension

variable (L)

abbrev RamifiedExtension (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsRamified K }

abbrev UnramifiedExtension (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsUnramified K }

variable {L v}


namespace RamifiedExtension


end RamifiedExtension

namespace UnramifiedExtension


end UnramifiedExtension

end NumberField.InfinitePlace
