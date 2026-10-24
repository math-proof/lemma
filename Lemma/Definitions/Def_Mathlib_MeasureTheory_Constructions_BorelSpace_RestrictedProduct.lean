import Mathlib

section

variable {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i)) (𝓕 : Filter ι)
  [(i : ι) → TopologicalSpace (R i)]

open scoped RestrictedProduct

instance : MeasurableSpace Πʳ (i : ι), [R i, A i]_[𝓕] := borel _

instance : BorelSpace Πʳ (i : ι), [R i, A i]_[𝓕] := ⟨rfl⟩
