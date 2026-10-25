import Mathlib
import Lemma.GroupCohomology.ContinuousH2
import Def.GroupCohomology_ContinuousH1
import Lemma.GroupCohomology.CupProduct

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
  (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  {M D N : Rep.{u} k G} (φ : M →ₗ[k] D →ₗ[k] N) (inv : continuousH2 r N →ₗ[k] k)

def IsTheta0 (θ : M.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D)) : Prop :=
  ∀ (m : M.ρ.invariants) (z : levelCocycles₂ r D) (e : levelCocycles₂ r N),
    (∀ st, (e : G × G → N) st = φ (m : M) ((z : G × G → D) st)) →
      θ m (continuousH2π r D z) = inv (continuousH2π r N e)

def IsTheta1 (θ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D)) : Prop :=
  ∀ (f : cocycles₁ M) (hf : IsLevelConstant₁ r (⇑f)) (g : cocycles₁ D) (hg : IsLevelConstant₁ r (⇑g))
    (e : levelCocycles₂ r N), (∀ st, (e : G × G → N) st = cupCochain φ (⇑f) (⇑g) st) →
      θ ⟨(H1π M).hom f, H1π_mem_continuousH1 r M hf⟩ ⟨(H1π D).hom g, H1π_mem_continuousH1 r D hg⟩
        = inv (continuousH2π r N e)

def IsTheta2 (θ : continuousH2 r M →ₗ[k] Module.Dual k D.ρ.invariants) : Prop :=
  ∀ (z : levelCocycles₂ r M) (d : D.ρ.invariants) (e : levelCocycles₂ r N),
    (∀ st, (e : G × G → N) st = φ ((z : G × G → M) st) (d : D)) →
      θ (continuousH2π r M z) d = inv (continuousH2π r N e)

end groupCohomology
