import Mathlib
import Instance.AbstractHeckeOperator
import Instance.LocalLanglands_HeckePair
import Lemma.Set.HeckeAlgebra

set_option autoImplicit false

open scoped Pointwise
open Function MulAction

namespace HeckePair

noncomputable section

variable {G : Type*} [Group G] (U : Subgroup G)
variable (R₀ : Type*) [CommRing R₀]

variable {U R₀}

theorem coe_mul (f₁ f₂ : HeckeAlgebra U R₀) :
    ((f₁ * f₂ : HeckeAlgebra U R₀) : G → R₀) = conv f₁ f₂ := rfl

theorem mul_apply (f₁ f₂ : HeckeAlgebra U R₀) (x : G) :
    ((f₁ * f₂ : HeckeAlgebra U R₀) : G → R₀) x = ∑ᶠ c : G ⧸ U, convTerm f₁ f₂ x c := rfl

theorem coe_one : ((1 : HeckeAlgebra U R₀) : G → R₀) = Set.indicator (U : Set G) 1 := rfl

theorem one_apply_of_mem {x : G} (hx : x ∈ U) : ((1 : HeckeAlgebra U R₀) : G → R₀) x = 1 :=
  Set.indicator_of_mem hx 1

theorem one_apply_of_notMem {x : G} (hx : x ∉ U) :
    ((1 : HeckeAlgebra U R₀) : G → R₀) x = 0 :=
  Set.indicator_of_notMem hx 1

theorem mem_doubleCoset_iff {g x : G} :
    x ∈ doubleCoset U g ↔ ∃ u ∈ U, ∃ v ∈ U, u * g * v = x := by
  constructor
  · rintro ⟨_, ⟨u, hu, _, rfl, rfl⟩, v, hv, rfl⟩
    exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨u * g, ⟨u, hu, g, rfl, rfl⟩, v, hv, rfl⟩

theorem self_mem_doubleCoset (g : G) : g ∈ doubleCoset U g :=
  mem_doubleCoset_iff.mpr ⟨1, one_mem U, 1, one_mem U, by group⟩

theorem mul_mem_doubleCoset {g x : G} (hx : x ∈ doubleCoset U g) {u : G} (hu : u ∈ U) :
    u * x ∈ doubleCoset U g := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp hx
  exact mem_doubleCoset_iff.mpr ⟨u * a, mul_mem hu ha, b, hb, by group⟩

theorem doubleCoset_mul_mem {g x : G} (hx : x ∈ doubleCoset U g) {u : G} (hu : u ∈ U) :
    x * u ∈ doubleCoset U g := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp hx
  exact mem_doubleCoset_iff.mpr ⟨a, ha, b * u, mul_mem hb hu, by group⟩

theorem image_mk_doubleCoset (g : G) :
    (QuotientGroup.mk '' (doubleCoset U g) : Set (G ⧸ U))
      = QuotientGroup.mk '' ((U : Set G) * {g}) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp hx
    refine ⟨a * g, ⟨a, ha, g, rfl, rfl⟩, QuotientGroup.eq.mpr ?_⟩
    rw [show (a * g)⁻¹ * (a * g * b) = b by group]
    exact hb
  · rintro _ ⟨w, ⟨a, ha, v, hv, rfl⟩, rfl⟩
    obtain rfl : v = g := hv
    exact ⟨a * v, mem_doubleCoset_iff.mpr ⟨a, ha, 1, one_mem U, by group⟩, rfl⟩

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

theorem heckeIndicator_apply_of_mem {g x : G} (hfin) (hx : x ∈ doubleCoset U g) :
    ((heckeIndicator R₀ g hfin : HeckeAlgebra U R₀) : G → R₀) x = 1 :=
  Set.indicator_of_mem hx 1

theorem heckeIndicator_apply_of_notMem {g x : G} (hfin) (hx : x ∉ doubleCoset U g) :
    ((heckeIndicator R₀ g hfin : HeckeAlgebra U R₀) : G → R₀) x = 0 :=
  Set.indicator_of_notMem hx 1

theorem heckeIndicator_of_mem {u : G} (hu : u ∈ U) (hfin) :
    heckeIndicator R₀ u hfin = (1 : HeckeAlgebra U R₀) := by
  ext x
  rw [coe_one]
  by_cases hx : x ∈ U
  · rw [heckeIndicator_apply_of_mem _ (mem_doubleCoset_iff.mpr
      ⟨x * u⁻¹, mul_mem hx (inv_mem hu), 1, one_mem U, by group⟩), Set.indicator_of_mem hx]
    rfl
  · rw [heckeIndicator_apply_of_notMem, Set.indicator_of_notMem hx]
    intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp h
    exact hx (mul_mem (mul_mem ha hu) hb)

end
end HeckePair
