import Mathlib
import Abbrev.NumberField_Extension
import Instance.NumberField_Extension
import Class.NumberField_Extension

section

noncomputable section

namespace NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
  (f : K →+* ℂ) (g : L →+* ℂ)


open scoped Classical in

def isExtensionEquivSum (f : K →+* ℂ) :
    { g : L →+* ℂ // IsExtension f g } ≃
      { g : L →+* ℂ // IsMixedExtension f g } ⊕ { g : L →+* ℂ // IsUnmixedExtension f g } :=
  (Equiv.sumCompl
    (fun g => ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g.1)).symm.trans <|
    Equiv.sumCongr
      (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun g => _ ∧ ¬ComplexEmbedding.IsReal g))
      ((Equiv.subtypeSubtypeEquivSubtypeInter _
        (fun g => ¬(_ ∧ ¬ComplexEmbedding.IsReal g))).trans
        (Equiv.subtypeEquiv (Equiv.refl _) (fun _ => by aesop)))

end NumberField.ComplexEmbedding

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] (v : InfinitePlace K) (w : InfinitePlace L)

variable [Algebra K L]


variable (L)

def Extension.toRamifiedExtension {w : v.Extension L} (h : w.1.IsRamified K) :
    v.RamifiedExtension L := ⟨w.1, ⟨w.2, h⟩⟩

def Extension.toUnramifiedExtension {w : v.Extension L} (h : w.1.IsUnramified K) :
    v.UnramifiedExtension L := ⟨w.1, ⟨w.2, h⟩⟩

end NumberField.InfinitePlace

end

end
