import Mathlib
import Instance.LocalLanglands_HeckePair

set_option autoImplicit false

open scoped Pointwise ENNReal
open MulAction MeasureTheory

namespace HeckeIntegralSeam

section CosetSystem

variable {G : Type*} [Group G]

structure IsHeckeCosetSystem (U : Subgroup G) (g : G) {ι : Type*} (reps : ι → G) : Prop where

  mem_doubleCoset : ∀ i, reps i ∈ HeckePair.doubleCoset U g

  covers : ∀ x ∈ HeckePair.doubleCoset U g,
    ∃ i, (QuotientGroup.mk x : G ⧸ U) = QuotientGroup.mk (reps i)

  mk_injective : Function.Injective fun i => (QuotientGroup.mk (reps i) : G ⧸ U)

variable {U : Subgroup G} {g : G}

end CosetSystem
end HeckeIntegralSeam
