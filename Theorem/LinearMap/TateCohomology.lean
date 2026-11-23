module

public import Mathlib
public import Abbrev.GroupCohomology_TateCohomology

public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

public theorem self_comp_norm' (g : G) : ρ g ∘ₗ ρ.norm = ρ.norm := by
  ext v
  simp only [norm, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => by
    simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]


public theorem norm_comp_self' (g : G) : ρ.norm ∘ₗ ρ g = ρ.norm := by
  ext v
  simp only [norm, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => by
    simp only [Equiv.coe_mulRight, map_mul, Module.End.mul_apply]


public theorem norm_apply_mem_invariants (v : V) : ρ.norm v ∈ ρ.invariants :=
  (mem_invariants ρ _).2 fun g => by
    rw [← LinearMap.comp_apply, self_comp_norm']


@[simp] public theorem coe_normToInvariants_apply (v : V) : (ρ.normToInvariants v : V) = ρ.norm v := rfl


public theorem normToInvariants_comp_self (g : G) : ρ.normToInvariants ∘ₗ ρ g = ρ.normToInvariants := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  change ρ.norm (ρ g v) = ρ.norm v
  rw [← LinearMap.comp_apply, norm_comp_self']


@[simp] public theorem normBar_mk (v : V) : ρ.normBar (Coinvariants.mk ρ v) = ρ.normToInvariants v := rfl


end Representation

namespace Rep

section lowDegrees

variable {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]


section maps

variable {A B C : Rep.{w} k G} (φ : A ⟶ B) (ψ : B ⟶ C)


@[simp] public theorem coe_invariantsMap_apply (a : A.ρ.invariants) : (invariantsMap φ a : B) = φ.hom a := rfl


public theorem coinvariantsMap_mk (a : A) :
    coinvariantsMap φ (Representation.Coinvariants.mk A.ρ a) = Representation.Coinvariants.mk B.ρ (φ.hom a) := rfl


public theorem hom_norm_apply (a : A) : φ.hom (A.ρ.norm a) = B.ρ.norm (φ.hom a) := by
  simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ => Rep.hom_comm_apply φ g a


public theorem normBar_comp_coinvariantsMap :
    B.ρ.normBar ∘ₗ coinvariantsMap φ = invariantsMap φ ∘ₗ A.ρ.normBar := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun a => Subtype.ext ?_)
  change B.ρ.norm (φ.hom a) = φ.hom (A.ρ.norm a)
  exact (hom_norm_apply φ a).symm


public theorem range_normBar_le_comap_invariantsMap :
    LinearMap.range A.ρ.normBar ≤ (LinearMap.range B.ρ.normBar).comap (invariantsMap φ) := by
  rintro x ⟨y, rfl⟩
  exact ⟨coinvariantsMap φ y, by rw [← LinearMap.comp_apply, normBar_comp_coinvariantsMap, LinearMap.comp_apply]⟩


@[simp] public theorem tateH0Map_mk (a : A.ρ.invariants) :
    tateH0Map φ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (invariantsMap φ a) := rfl


@[simp] public theorem coe_tateHneg1Map_apply (x : A.tateHneg1) :
    (tateHneg1Map φ x : B.ρ.Coinvariants) = coinvariantsMap φ x := rfl


public theorem tateH0Map_id : tateH0Map (𝟙 A) = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
  change Submodule.Quotient.mk (invariantsMap (𝟙 A) a) = Submodule.Quotient.mk a
  congr 1


public theorem tateH0Map_comp : tateH0Map (φ ≫ ψ) = tateH0Map ψ ∘ₗ tateH0Map φ := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
  change Submodule.Quotient.mk (invariantsMap (φ ≫ ψ) a) =
    Submodule.Quotient.mk (invariantsMap ψ (invariantsMap φ a))
  congr 1


public theorem tateHneg1Map_id : tateHneg1Map (𝟙 A) = LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x : A.ρ.Coinvariants)
  simp only [LinearMap.id_apply, coe_tateHneg1Map_apply]
  rw [← ha]
  rfl


public theorem tateHneg1Map_comp : tateHneg1Map (φ ≫ ψ) = tateHneg1Map ψ ∘ₗ tateHneg1Map φ := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x : A.ρ.Coinvariants)
  simp only [LinearMap.comp_apply, coe_tateHneg1Map_apply]
  rw [← ha]
  rfl

end maps

end lowDegrees

section graded

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]


public theorem tateCohomology_ofNat_succ (A : Rep.{u} k G) (n : ℕ) : A.tateCohomology (n + 1 : ℕ) = groupCohomology A (n + 1) := rfl

public theorem tateCohomology_zero (A : Rep.{u} k G) : A.tateCohomology 0 = ModuleCat.of k A.tateH0 := rfl

public theorem tateCohomology_neg_one (A : Rep.{u} k G) : A.tateCohomology (-1) = ModuleCat.of k A.tateHneg1 := rfl

public theorem tateCohomology_negSucc_succ (A : Rep.{u} k G) (n : ℕ) :
    A.tateCohomology (Int.negSucc (n + 1)) = groupHomology A (n + 1) := rfl

end graded

end Rep
