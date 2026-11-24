module
public import Mathlib
public import Theorem.Submodule.ContinuousH2
public import Theorem.Rep.ContinuousH2Map
public import Def.GroupCohomology_ContinuousH1
public import Abbrev.GroupCohomology_ContinuousH1
set_option autoImplicit false


public section

universe u

open CategoryTheory

noncomputable section

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
  (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

section carriers

variable (M : Rep k G)


theorem mem_levelCocycles₁_iff (c : cocycles₁ M) : c ∈ levelCocycles₁ r M ↔ IsLevelConstant₁ r c :=
  Iff.rfl


theorem mem_continuousH1_iff (x : H1 M) :
    x ∈ continuousH1 r M ↔ ∃ c : cocycles₁ M, IsLevelConstant₁ r c ∧ (H1π M).hom c = x := by
  simp only [continuousH1, Submodule.mem_map, mem_levelCocycles₁_iff]

theorem H1π_mem_continuousH1 {c : cocycles₁ M} (hc : IsLevelConstant₁ r c) :
    (H1π M).hom c ∈ continuousH1 r M :=
  (mem_continuousH1_iff r M _).2 ⟨c, hc, rfl⟩

theorem eq_continuousH1_of_forall_mem_iff (adm₁ : Submodule k (H1 M))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔ ∃ c : cocycles₁ M,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : G), r s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (H1π M).hom c = x) :
    adm₁ = continuousH1 r M := by
  ext x
  rw [hadm₁, mem_continuousH1_iff]
  rfl

end carriers

section delta

variable {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)


theorem apply_preimageFun {b : B} (h : ∃ a : A, φ.hom a = b) : φ.hom (preimageFun φ b) = b := by
  rw [preimageFun, dite_eq_left h]; exact h.choose_spec

theorem preimageFun_apply (hφ : Function.Injective φ.hom) (a : A) : preimageFun φ (φ.hom a) = a :=
  hφ (apply_preimageFun φ ⟨a, rfl⟩)

variable (hψ : Function.Surjective ψ.hom)


theorem deltaCochain₀_apply (c : C) (g : G) :
    deltaCochain₀ φ ψ hψ c g = preimageFun φ (B.ρ g (Function.surjInv hψ c) - Function.surjInv hψ c) := by
  rw [deltaCochain₀, d₀₁_hom_apply]

theorem deltaCochain₁_apply (c : G → C) (g h : G) :
    deltaCochain₁ φ ψ hψ c (g, h) = preimageFun φ
      (B.ρ g (Function.surjInv hψ (c h)) - Function.surjInv hψ (c (g * h)) + Function.surjInv hψ (c g)) := by
  rw [deltaCochain₁, d₁₂_hom_apply]; rfl

end delta

end groupCohomology

end
