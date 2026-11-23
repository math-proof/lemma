module

public import Mathlib
public import Abbrev.GroupCohomology_TateCohomology

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

noncomputable def normToInvariants : V →ₗ[k] ρ.invariants :=
  LinearMap.codRestrict ρ.invariants ρ.norm (norm_apply_mem_invariants ρ)

noncomputable def normBar : ρ.Coinvariants →ₗ[k] ρ.invariants :=
  Coinvariants.lift ρ ρ.normToInvariants (normToInvariants_comp_self ρ)

end Representation

namespace Rep

section lowDegrees

variable {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]


section maps

variable {A B C : Rep.{w} k G} (φ : A ⟶ B) (ψ : B ⟶ C)

noncomputable def tateH0Map : A.tateH0 →ₗ[k] B.tateH0 :=
  Submodule.mapQ _ _ (invariantsMap φ) (range_normBar_le_comap_invariantsMap φ)

noncomputable def tateHneg1Map : A.tateHneg1 →ₗ[k] B.tateHneg1 :=
  (coinvariantsMap φ ∘ₗ (LinearMap.ker A.ρ.normBar).subtype).codRestrict _ (fun x => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.comp_apply (f := B.ρ.normBar),
      normBar_comp_coinvariantsMap, LinearMap.comp_apply, Submodule.subtype_apply, x.2, map_zero])

end maps

end lowDegrees

section graded

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

noncomputable def tateCohomology (A : Rep.{u} k G) : ℤ → ModuleCat.{u} k
  | (Int.ofNat (n + 1)) => groupCohomology A (n + 1)
  | (Int.ofNat 0) => ModuleCat.of k A.tateH0
  | (Int.negSucc 0) => ModuleCat.of k A.tateHneg1
  | (Int.negSucc (n + 1)) => groupHomology A (n + 1)

end graded

end Rep

end
