module

public import Mathlib
public import Instance.AbstractHeckeOperator
public import Instance.LocalLanglands_HeckePair
public import Def.Set_HeckeAlgebra

@[expose] public section

set_option autoImplicit false

open scoped Pointwise
open Function MulAction

namespace HeckePair

noncomputable section

variable {G : Type*} [Group G] (U : Subgroup G)
variable (R₀ : Type*) [CommRing R₀]

variable {U R₀}

variable (R₀) in

def heckeIndicator (g : G) (hfin : (QuotientGroup.mk '' ((U : Set G) * {g})
    : Set (G ⧸ U)).Finite) : HeckeAlgebra U R₀ :=
  ⟨Set.indicator (doubleCoset U g) 1, by
    refine ⟨fun u hu x => ?_, fun u hu x => ?_, ?_⟩
    · by_cases hx : x ∈ doubleCoset U g
      · simp only [Set.indicator_of_mem (mul_mem_doubleCoset hx hu), Set.indicator_of_mem hx,
          Pi.one_apply]
      · rw [Set.indicator_of_notMem (fun h => hx ?_), Set.indicator_of_notMem hx]
        simpa using mul_mem_doubleCoset h (inv_mem hu)
    · by_cases hx : x ∈ doubleCoset U g
      · simp only [Set.indicator_of_mem (doubleCoset_mul_mem hx hu), Set.indicator_of_mem hx,
          Pi.one_apply]
      · rw [Set.indicator_of_notMem (fun h => hx ?_), Set.indicator_of_notMem hx]
        simpa using doubleCoset_mul_mem h (inv_mem hu)
    · rw [← image_mk_doubleCoset] at hfin
      refine hfin.subset (Set.image_mono ?_)
      intro y hy
      by_contra hyD
      exact hy (Set.indicator_of_notMem hyD 1)⟩

end
end HeckePair
