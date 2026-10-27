import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.EllipticCurves.code.Theorem161
open ComplexLattice
open Pointwise Function ZSpan


namespace ComplexLattice

/--
[proj_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma proj_eq_iff
  {L : ComplexLattice}
  {z w : ℂ} :
-- imply
  proj L z = proj L w ↔ ∃ v ∈ L.lattice.toAddSubgroup, z + v = w :=
-- proof
  QuotientAddGroup.mk'_eq_mk' L.lattice.toAddSubgroup

end ComplexLattice

namespace ComplexLattice

/--
[proj_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma proj_eq_zero_iff
  {L : ComplexLattice}
  {z : ℂ} :
-- imply
  proj L z = 0 ↔ z ∈ L.lattice.toAddSubgroup :=
-- proof
  QuotientAddGroup.eq_zero_iff z

end ComplexLattice

namespace ComplexLattice

/--
[mem_latticeMulSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma mem_latticeMulSet_iff
  {L₁ L₂ : ComplexLattice}
  {α : ℂ} :
-- imply
  α ∈ latticeMulSet L₁ L₂ ↔ ∀ z ∈ (L₁.lattice : Set ℂ), α * z ∈ (L₂.lattice : Set ℂ) :=
-- proof
  Iff.rfl

end ComplexLattice

namespace ComplexLattice

/--
[inducedMap_proj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma inducedMap_proj
  {L₁ L₂ : ComplexLattice}
  {α : ℂ}
  {z : ℂ}
-- given
  (hα : α ∈ latticeMulSet L₁ L₂) :
-- imply
  inducedMap L₁ L₂ α hα (proj L₁ z) = proj L₂ (α * z) := by
-- proof
  simp only [inducedMap, proj, mulByAlphaHom, QuotientAddGroup.lift_mk',
    AddMonoidHom.comp_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    QuotientAddGroup.mk'_apply]

end ComplexLattice

namespace ComplexLattice

/--
[const_of_continuous_latticeValued](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma const_of_continuous_latticeValued
  {L : ComplexLattice}
  {g : ℂ → ℂ}
-- given
  (hg : Continuous g)
  (himg : ∀ z, g z ∈ (L.lattice : Set ℂ)) :
-- imply
  ∀ x y, g x = g y := by
-- proof
  let g' : ℂ → L.lattice := fun z => ⟨g z, himg z⟩
  have hg' : Continuous g' := continuous_induced_rng.mpr hg
  intro x y
  have h := @PreconnectedSpace.constant ℂ _ L.lattice _ _ inferInstance g' hg' x y
  exact congrArg Subtype.val h

end ComplexLattice

namespace ComplexLattice

/--
[deriv_periodic_of_shift_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma deriv_periodic_of_shift_const
  {f : ℂ → ℂ}
  {ω : ℂ}
  {c : ℂ}
-- given
  (hc : ∀ z, f (z + ω) = f z + c) :
-- imply
  ∀ z, deriv f (z + ω) = deriv f z := by
-- proof
  intro z
  have h1 : deriv (fun x => f (x + ω)) z = deriv f (z + ω) := deriv_comp_add_const f ω z
  have h2 : deriv (fun x => f x + c) z = deriv f z := deriv_add_const c
  have h3 : (fun x => f (x + ω)) = (fun x => f x + c) := funext hc
  rw [← h1, ← h2, h3]

end ComplexLattice

namespace ComplexLattice

/--
[affine_of_const_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma affine_of_const_deriv
  {f : ℂ → ℂ}
  {α : ℂ}
-- given
  (hf : Differentiable ℂ f)
  (hderiv_eq : ∀ w, deriv f w = α) :
-- imply
  ∀ z, f z = α * z + f 0 := by
-- proof
  intro z
  let g : ℂ → ℂ := fun z => f z - (α * z + f 0)
  suffices h : g z = g 0 by
    simp only [g, mul_zero, zero_add, sub_self] at h
    linear_combination h
  apply is_const_of_deriv_eq_zero
  · exact hf.sub ((differentiable_const α).mul differentiable_id |>.add (differentiable_const _))
  · intro w
    have hfw : HasDerivAt f α w := by rw [← hderiv_eq]; exact (hf w).hasDerivAt
    have haw : HasDerivAt (fun z => α * z + f 0) α w := by
      have h1 : HasDerivAt (fun z => α * z) α w := by
        have := (hasDerivAt_id w).const_mul α
        simp only [mul_one] at this; exact this
      simpa only [add_zero] using h1.add (hasDerivAt_const w (f 0))
    have : HasDerivAt g 0 w := by
      simpa only [sub_self] using hfw.sub haw
    exact this.deriv

end ComplexLattice

namespace ComplexLattice

/--
[periodic_of_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma periodic_of_generators
  {f : ℂ → ℂ}
  {L : ComplexLattice}
-- given
  (hp1 : Periodic f L.ω₁)
  (hp2 : Periodic f L.ω₂) :
-- imply
  ∀ z w, w ∈ L.lattice → f (z + w) = f z := by
-- proof
  intro z w hw
  rw [ComplexLattice.mem_lattice_iff] at hw
  obtain ⟨n₁, n₂, rfl⟩ := hw
  have hper1 : Periodic f ((n₁ : ℂ) * L.ω₁) := hp1.int_mul n₁
  have hper2 : Periodic f ((n₂ : ℂ) * L.ω₂) := hp2.int_mul n₂
  calc f (z + ((n₁ : ℂ) * L.ω₁ + (n₂ : ℂ) * L.ω₂))
    = f (z + (n₁ : ℂ) * L.ω₁ + (n₂ : ℂ) * L.ω₂) := by rw [add_assoc]
    _ = f (z + (n₁ : ℂ) * L.ω₁) := hper2 _
    _ = f z := hper1 _

end ComplexLattice

namespace ComplexLattice

/--
[entire_periodic_isBounded_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma entire_periodic_isBounded_range
  {f : ℂ → ℂ}
  {L : ComplexLattice}
-- given
  (hf : Differentiable ℂ f)
  (hp1 : Periodic f L.ω₁)
  (hp2 : Periodic f L.ω₂) :
-- imply
  Bornology.IsBounded (Set.range f) := by
-- proof
  have hper : ∀ z w, w ∈ L.lattice → f (z + w) = f z :=
    periodic_of_generators f L hp1 hp2
  exact (IsZLattice.isCompact_range_of_periodic L.lattice f hf.continuous hper).isBounded

end ComplexLattice

namespace ComplexLattice

/--
[theorem_16_1_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma theorem_16_1_existence
  {L₁ L₂ : ComplexLattice}
  {φ : ComplexTorusHolMap L₁ L₂}
-- given
  (hφ0 : φ.toFun 0 = 0) :
-- imply
  ∃ α : ℂ, ∃ hα : α ∈ latticeMulSet L₁ L₂, ∀ z : ℂ, φ.toFun (proj L₁ z) = inducedMap L₁ L₂ α hα (proj L₁ z) := by
-- proof
  set f := φ.lift with hf_def
  have hf := φ.lift_differentiable
  have hcomm := φ.diagram_commutes
  have hshift : ∀ ω ∈ (L₁.lattice : Set ℂ), ∀ z, f (z + ω) - f z ∈ (L₂.lattice : Set ℂ) := by
    intro ω hω z
    have hπ : proj L₁ (z + ω) = proj L₁ z := by
      rw [map_add]
      have : proj L₁ ω = 0 := (proj_eq_zero_iff L₁ ω).mpr hω
      rw [this, add_zero]
    have : proj L₂ (f (z + ω)) = proj L₂ (f z) := by
      rw [← hcomm (z + ω), ← hcomm z, hπ]
    rwa [← sub_eq_zero, ← map_sub, proj_eq_zero_iff] at this
  have hconst : ∀ ω ∈ (L₁.lattice : Set ℂ), ∀ z, f (z + ω) - f z = f ω - f 0 := by
    intro ω hω z
    have hcont : Continuous (fun z => f (z + ω) - f z) :=
      (hf.comp (differentiable_id.add (differentiable_const ω))).continuous.sub hf.continuous
    have := const_of_continuous_latticeValued L₂ _ hcont (hshift ω hω) z 0
    simp only [zero_add] at this
    exact this
  have hderiv_per : ∀ ω ∈ (L₁.lattice : Set ℂ), ∀ z, deriv f (z + ω) = deriv f z := by
    intro ω hω z
    apply deriv_periodic_of_shift_const f ω (f ω - f 0) (fun w => ?_) z
    have := hconst ω hω w
    linear_combination this
  have hp1 : Periodic (deriv f) L₁.ω₁ :=
    fun z => hderiv_per L₁.ω₁ (ComplexLattice.ω₁_mem L₁) z
  have hp2 : Periodic (deriv f) L₁.ω₂ :=
    fun z => hderiv_per L₁.ω₂ (ComplexLattice.ω₂_mem L₁) z
  have hdf : Differentiable ℂ (deriv f) :=
    (hf.contDiff (n := 2)).differentiable_deriv_two
  have hbdd := entire_periodic_isBounded_range (deriv f) hdf L₁ hp1 hp2
  have hconst_deriv : ∀ z w, deriv f z = deriv f w :=
    fun z w => hdf.apply_eq_apply_of_bounded hbdd z w
  set α := deriv f 0
  have haffine := affine_of_const_deriv f hf α (fun w => hconst_deriv w 0)
  have hf0 : f 0 ∈ (L₂.lattice : Set ℂ) := by
    have : proj L₂ (f 0) = 0 := by rw [← hcomm 0, map_zero, hφ0]
    rwa [proj_eq_zero_iff] at this
  have hα_mem : α ∈ latticeMulSet L₁ L₂ := by
    intro ω hω
    have hfω_sub : f ω - f 0 ∈ (L₂.lattice : Set ℂ) := by
      have := hshift ω hω 0; simp only [zero_add] at this; exact this
    have : f ω - f 0 = α * ω := by
      have := haffine ω; linear_combination this
    rwa [this] at hfω_sub
  refine ⟨α, hα_mem, fun z => ?_⟩
  show φ.toFun (proj L₁ z) = inducedMap L₁ L₂ α hα_mem (proj L₁ z)
  rw [hcomm z, inducedMap_proj]
  have hfz : φ.lift z = α * z + f 0 := haffine z
  rw [hfz, map_add]
  have : proj L₂ (f 0) = 0 := (proj_eq_zero_iff L₂ (f 0)).mpr hf0
  rw [this, add_zero]

end ComplexLattice

namespace ComplexLattice

/--
[inducedMap_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma inducedMap_unique
  {L₁ L₂ : ComplexLattice}
  {α γ : ℂ}
-- given
  (hα : α ∈ latticeMulSet L₁ L₂)
  (hγ : γ ∈ latticeMulSet L₁ L₂)
  (heq : ∀ z : ℂ, inducedMap L₁ L₂ α hα (proj L₁ z) = inducedMap L₁ L₂ γ hγ (proj L₁ z)) :
-- imply
  α = γ := by
-- proof
  have hproj : ∀ z, proj L₂ (α * z) = proj L₂ (γ * z) := by
    intro z; rw [← inducedMap_proj L₁ L₂ α hα, ← inducedMap_proj L₁ L₂ γ hγ]; exact heq z
  have hdiff : ∀ z, (α - γ) * z ∈ (L₂.lattice : Set ℂ) := by
    intro z
    have h := hproj z
    rw [proj_eq_iff] at h
    obtain ⟨v, hv, hvz⟩ := h
    have hv_eq : (α - γ) * z = -v := by
      have : v = γ * z - α * z := by linear_combination hvz
      rw [this]; ring
    rw [hv_eq]
    exact L₂.lattice.toAddSubgroup.neg_mem hv
  have hconst := const_of_continuous_latticeValued L₂ (fun z => (α - γ) * z)
    (continuous_const.mul continuous_id) hdiff
  have h0 := hconst 1 0
  simp only [mul_one, mul_zero] at h0
  exact sub_eq_zero.mp h0

end ComplexLattice

namespace ComplexLattice

/--
[theorem_16_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma theorem_16_1
  {L₁ L₂ : ComplexLattice}
  {φ : ComplexTorusHolMap L₁ L₂}
-- given
  (hφ0 : φ.toFun 0 = 0) :
-- imply
  ∃! α : ℂ, ∃ hα : α ∈ latticeMulSet L₁ L₂, ∀ z : ℂ, φ.toFun (proj L₁ z) = inducedMap L₁ L₂ α hα (proj L₁ z) := by
-- proof
  obtain ⟨α, hα, hφα⟩ := theorem_16_1_existence L₁ L₂ φ hφ0
  refine ⟨α, ⟨hα, hφα⟩, ?_⟩
  intro γ ⟨hγ, hφγ⟩
  exact (inducedMap_unique L₁ L₂ α γ hα hγ (fun z => by rw [← hφα z, ← hφγ z])).symm

end ComplexLattice

namespace ComplexLattice

/--
[add_mem_latticeMulSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma add_mem_latticeMulSet
  {L₁ L₂ : ComplexLattice}
  {α β : ℂ}
-- given
  (hα : α ∈ latticeMulSet L₁ L₂)
  (hβ : β ∈ latticeMulSet L₁ L₂) :
-- imply
  α + β ∈ latticeMulSet L₁ L₂ := by
-- proof
  intro z hz
  have : (α + β) * z = α * z + β * z := add_mul α β z
  rw [this]
  exact L₂.lattice.add_mem (hα z hz) (hβ z hz)

end ComplexLattice

namespace ComplexLattice

/--
[inducedMap_add_proj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma inducedMap_add_proj
  {L₁ L₂ : ComplexLattice}
  {α β : ℂ}
-- given
  (hα : α ∈ latticeMulSet L₁ L₂)
  (hβ : β ∈ latticeMulSet L₁ L₂) :
-- imply
  ∀ z : ℂ, inducedMap L₁ L₂ (α + β) (add_mem_latticeMulSet L₁ L₂ α β hα hβ) (proj L₁ z) = inducedMap L₁ L₂ α hα (proj L₁ z) + inducedMap L₁ L₂ β hβ (proj L₁ z) := by
-- proof
  intro z
  simp only [inducedMap_proj]
  rw [show (α + β) * z = α * z + β * z from add_mul α β z]
  exact map_add (proj L₂) (α * z) (β * z)

end ComplexLattice

namespace ComplexLattice

/--
[latticeMulSet_to_torusMorphism_addGroupIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma latticeMulSet_to_torusMorphism_addGroupIso
  {L₁ L₂ : ComplexLattice} :
-- imply
  (∀ (α β : ℂ) (hα : α ∈ latticeMulSet L₁ L₂) (hβ : β ∈ latticeMulSet L₁ L₂), ∀ z : ℂ, inducedMap L₁ L₂ (α + β) (add_mem_latticeMulSet L₁ L₂ α β hα hβ) (proj L₁ z) = inducedMap L₁ L₂ α hα (proj L₁ z) + inducedMap L₁ L₂ β hβ (proj L₁ z)) ∧ (∀ z : ℂ, inducedMap L₁ L₂ 0 (zero_mem_latticeMulSet L₁ L₂) (proj L₁ z) = 0) ∧ (∀ (α γ : ℂ) (hα : α ∈ latticeMulSet L₁ L₂) (hγ : γ ∈ latticeMulSet L₁ L₂), (∀ z : ℂ, inducedMap L₁ L₂ α hα (proj L₁ z) = inducedMap L₁ L₂ γ hγ (proj L₁ z)) → α = γ) ∧ (∀ (φ : ComplexTorusHolMap L₁ L₂), φ.toFun 0 = 0 → ∃ α : ℂ, ∃ hα : α ∈ latticeMulSet L₁ L₂, ∀ z : ℂ, φ.toFun (proj L₁ z) = inducedMap L₁ L₂ α hα (proj L₁ z)) := by
-- proof
  refine ⟨fun α β hα hβ => inducedMap_add_proj L₁ L₂ α β hα hβ, fun z => ?_,
    fun α γ hα hγ => inducedMap_unique L₁ L₂ α γ hα hγ,
    fun φ hφ0 => theorem_16_1_existence L₁ L₂ φ hφ0⟩
  simp only [inducedMap_proj, zero_mul, map_zero]

end ComplexLattice

namespace ComplexLattice

/--
[mul_mem_latticeMulSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma mul_mem_latticeMulSet
  {L : ComplexLattice}
  {α β : ℂ}
-- given
  (hα : α ∈ latticeMulSet L L)
  (hβ : β ∈ latticeMulSet L L) :
-- imply
  α * β ∈ latticeMulSet L L := by
-- proof
  intro z hz
  have : α * β * z = α * (β * z) := mul_assoc α β z
  rw [this]
  exact hα (β * z) (hβ z hz)

end ComplexLattice

namespace ComplexLattice

/--
[one_mem_latticeMulSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma one_mem_latticeMulSet
  {L : ComplexLattice} :
-- imply
  (1 : ℂ) ∈ latticeMulSet L L := by
-- proof
  intro z hz; simp; exact hz

end ComplexLattice

namespace ComplexLattice

/--
[inducedMap_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
lemma inducedMap_comp
  {L : ComplexLattice}
  {α β : ℂ}
-- given
  (hα : α ∈ latticeMulSet L L)
  (hβ : β ∈ latticeMulSet L L) :
-- imply
  ∀ z : ℂ, inducedMap L L (α * β) (mul_mem_latticeMulSet L α β hα hβ) (proj L z) = (inducedMap L L α hα) (inducedMap L L β hβ (proj L z)) := by
-- proof
  intro z
  simp only [inducedMap_proj]
  rw [show α * β * z = α * (β * z) from mul_assoc α β z]
end


/--
[zero_mem_latticeMulSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean)
-/
@[path]
private lemma zero_mem_latticeMulSet_eq
  {L₁ L₂ : ComplexLattice} :
-- imply
  (0 : ℂ) ∈ latticeMulSet L₁ L₂ := by
-- proof
  apply ComplexLattice.zero_mem_latticeMulSet L₁ L₂


-- created on 2026-10-23
