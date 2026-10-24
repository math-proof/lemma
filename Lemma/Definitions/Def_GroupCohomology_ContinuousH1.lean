import Mathlib
import Lemma.Definitions.Def_GroupCohomology_ContinuousH2
import Lemma.Definitions.Def_GroupCohomology_ContinuousH2Map

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
  (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

section carriers

variable (M : Rep k G)

def levelCocycles₁ : Submodule k (cocycles₁ M) :=
  (levelCochains₁ r M).comap (cocycles₁ M).subtype

lemma mem_levelCocycles₁_iff (c : cocycles₁ M) : c ∈ levelCocycles₁ r M ↔ IsLevelConstant₁ r c :=
  Iff.rfl

def continuousH1 : Submodule k (H1 M) :=
  (levelCocycles₁ r M).map (H1π M).hom

lemma mem_continuousH1_iff (x : H1 M) :
    x ∈ continuousH1 r M ↔ ∃ c : cocycles₁ M, IsLevelConstant₁ r c ∧ (H1π M).hom c = x := by
  simp only [continuousH1, Submodule.mem_map, mem_levelCocycles₁_iff]

lemma H1π_mem_continuousH1 {c : cocycles₁ M} (hc : IsLevelConstant₁ r c) :
    (H1π M).hom c ∈ continuousH1 r M :=
  (mem_continuousH1_iff r M _).2 ⟨c, hc, rfl⟩

lemma eq_continuousH1_of_forall_mem_iff (adm₁ : Submodule k (H1 M))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔ ∃ c : cocycles₁ M,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : G), r s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (H1π M).hom c = x) :
    adm₁ = continuousH1 r M := by
  ext x
  rw [hadm₁, mem_continuousH1_iff]
  rfl

end carriers

abbrev continuousH2MapHom {A B : Rep k G} (φ : A ⟶ B) : continuousH2 r A →ₗ[k] continuousH2 r B :=
  continuousH2Map (MonoidHom.id G) (fun _ => rfl) φ.hom.toLinearMap (fun g a => Rep.hom_comm_apply φ g a)

section delta

variable {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)

open Classical in

def preimageFun (b : B) : A :=
  if h : ∃ a : A, φ.hom a = b then h.choose else 0

lemma apply_preimageFun {b : B} (h : ∃ a : A, φ.hom a = b) : φ.hom (preimageFun φ b) = b := by
  rw [preimageFun, dif_pos h]; exact h.choose_spec

lemma preimageFun_apply (hφ : Function.Injective φ.hom) (a : A) : preimageFun φ (φ.hom a) = a :=
  hφ (apply_preimageFun φ ⟨a, rfl⟩)

variable (hψ : Function.Surjective ψ.hom)

def deltaCochain₀ (c : C) : G → A :=
  fun g => preimageFun φ ((d₀₁ B).hom (Function.surjInv hψ c) g)

def deltaCochain₁ (c : G → C) : G × G → A :=
  fun p => preimageFun φ ((d₁₂ B).hom (Function.surjInv hψ ∘ c) p)

lemma deltaCochain₀_apply (c : C) (g : G) :
    deltaCochain₀ φ ψ hψ c g = preimageFun φ (B.ρ g (Function.surjInv hψ c) - Function.surjInv hψ c) := by
  rw [deltaCochain₀, d₀₁_hom_apply]

lemma deltaCochain₁_apply (c : G → C) (g h : G) :
    deltaCochain₁ φ ψ hψ c (g, h) = preimageFun φ
      (B.ρ g (Function.surjInv hψ (c h)) - Function.surjInv hψ (c (g * h)) + Function.surjInv hψ (c g)) := by
  rw [deltaCochain₁, d₁₂_hom_apply]; rfl

end delta

end groupCohomology

end
