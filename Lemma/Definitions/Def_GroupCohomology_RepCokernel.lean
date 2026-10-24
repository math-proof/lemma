import Mathlib

set_option autoImplicit false

open CategoryTheory

namespace GroupCohomology.RepCokernel

universe u

variable {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)

noncomputable abbrev obj : Rep.{u} k G :=
  Rep.of (Representation.quotient Y.ρ (LinearMap.range f.hom.toLinearMap) fun g => by
    rintro _ ⟨a, rfl⟩
    exact ⟨X.ρ g a, Rep.hom_comm_apply f g a⟩)

noncomputable def π : Y ⟶ obj f := Rep.ofHom ⟨Submodule.mkQ _, fun _ => rfl⟩

theorem π_hom_apply (y : Y) : (π f).hom y = Submodule.Quotient.mk y := rfl

theorem π_hom_surjective : Function.Surjective (π f).hom := Submodule.mkQ_surjective _

theorem π_hom_apply_eq_zero_iff (y : Y) : (π f).hom y = 0 ↔ y ∈ LinearMap.range f.hom.toLinearMap :=
  Submodule.Quotient.mk_eq_zero _

noncomputable def seq : ShortComplex (Rep.{u} k G) where
  X₁ := X
  X₂ := Y
  X₃ := obj f
  f := f
  g := π f
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩))

end GroupCohomology.RepCokernel
