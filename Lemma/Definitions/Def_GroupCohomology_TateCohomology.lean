import Mathlib

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

lemma self_comp_norm' (g : G) : ρ g ∘ₗ ρ.norm = ρ.norm := by
  ext v
  simp only [norm, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => by
    simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]

lemma norm_comp_self' (g : G) : ρ.norm ∘ₗ ρ g = ρ.norm := by
  ext v
  simp only [norm, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => by
    simp only [Equiv.coe_mulRight, map_mul, Module.End.mul_apply]

lemma norm_apply_mem_invariants (v : V) : ρ.norm v ∈ ρ.invariants :=
  (mem_invariants ρ _).2 fun g => by
    rw [← LinearMap.comp_apply, self_comp_norm']

noncomputable def normToInvariants : V →ₗ[k] ρ.invariants :=
  LinearMap.codRestrict ρ.invariants ρ.norm (norm_apply_mem_invariants ρ)

@[simp] lemma coe_normToInvariants_apply (v : V) : (ρ.normToInvariants v : V) = ρ.norm v := rfl

lemma normToInvariants_comp_self (g : G) : ρ.normToInvariants ∘ₗ ρ g = ρ.normToInvariants := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  change ρ.norm (ρ g v) = ρ.norm v
  rw [← LinearMap.comp_apply, norm_comp_self']

noncomputable def normBar : ρ.Coinvariants →ₗ[k] ρ.invariants :=
  Coinvariants.lift ρ ρ.normToInvariants (normToInvariants_comp_self ρ)

@[simp] lemma normBar_mk (v : V) : ρ.normBar (Coinvariants.mk ρ v) = ρ.normToInvariants v := rfl

abbrev tateH0 : Type _ := ρ.invariants ⧸ LinearMap.range ρ.normBar

abbrev tateHneg1 : Type _ := LinearMap.ker ρ.normBar

end Representation

namespace Rep

section lowDegrees

variable {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]

abbrev tateH0 (A : Rep.{w} k G) : Type w := A.ρ.tateH0

abbrev tateHneg1 (A : Rep.{w} k G) : Type w := A.ρ.tateHneg1

section maps

variable {A B C : Rep.{w} k G} (φ : A ⟶ B) (ψ : B ⟶ C)

noncomputable abbrev invariantsMap : A.ρ.invariants →ₗ[k] B.ρ.invariants :=
  ((Rep.invariantsFunctor k G).map φ).hom

omit [Fintype G] in
@[simp] lemma coe_invariantsMap_apply (a : A.ρ.invariants) : (invariantsMap φ a : B) = φ.hom a := rfl

noncomputable abbrev coinvariantsMap : A.ρ.Coinvariants →ₗ[k] B.ρ.Coinvariants :=
  ((Rep.coinvariantsFunctor k G).map φ).hom

omit [Fintype G] in
lemma coinvariantsMap_mk (a : A) :
    coinvariantsMap φ (Representation.Coinvariants.mk A.ρ a) = Representation.Coinvariants.mk B.ρ (φ.hom a) := rfl

lemma hom_norm_apply (a : A) : φ.hom (A.ρ.norm a) = B.ρ.norm (φ.hom a) := by
  simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ => Rep.hom_comm_apply φ g a

lemma normBar_comp_coinvariantsMap :
    B.ρ.normBar ∘ₗ coinvariantsMap φ = invariantsMap φ ∘ₗ A.ρ.normBar := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun a => Subtype.ext ?_)
  change B.ρ.norm (φ.hom a) = φ.hom (A.ρ.norm a)
  exact (hom_norm_apply φ a).symm

lemma range_normBar_le_comap_invariantsMap :
    LinearMap.range A.ρ.normBar ≤ (LinearMap.range B.ρ.normBar).comap (invariantsMap φ) := by
  rintro x ⟨y, rfl⟩
  exact ⟨coinvariantsMap φ y, by rw [← LinearMap.comp_apply, normBar_comp_coinvariantsMap, LinearMap.comp_apply]⟩

noncomputable def tateH0Map : A.tateH0 →ₗ[k] B.tateH0 :=
  Submodule.mapQ _ _ (invariantsMap φ) (range_normBar_le_comap_invariantsMap φ)

@[simp] lemma tateH0Map_mk (a : A.ρ.invariants) :
    tateH0Map φ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (invariantsMap φ a) := rfl

noncomputable def tateHneg1Map : A.tateHneg1 →ₗ[k] B.tateHneg1 :=
  (coinvariantsMap φ ∘ₗ (LinearMap.ker A.ρ.normBar).subtype).codRestrict _ (fun x => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.comp_apply (f := B.ρ.normBar),
      normBar_comp_coinvariantsMap, LinearMap.comp_apply, Submodule.subtype_apply, x.2, map_zero])

@[simp] lemma coe_tateHneg1Map_apply (x : A.tateHneg1) :
    (tateHneg1Map φ x : B.ρ.Coinvariants) = coinvariantsMap φ x := rfl

lemma tateH0Map_id : tateH0Map (𝟙 A) = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
  change Submodule.Quotient.mk (invariantsMap (𝟙 A) a) = Submodule.Quotient.mk a
  congr 1

lemma tateH0Map_comp : tateH0Map (φ ≫ ψ) = tateH0Map ψ ∘ₗ tateH0Map φ := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
  change Submodule.Quotient.mk (invariantsMap (φ ≫ ψ) a) =
    Submodule.Quotient.mk (invariantsMap ψ (invariantsMap φ a))
  congr 1

lemma tateHneg1Map_id : tateHneg1Map (𝟙 A) = LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x : A.ρ.Coinvariants)
  simp only [LinearMap.id_apply, coe_tateHneg1Map_apply]
  rw [← ha]
  rfl

lemma tateHneg1Map_comp : tateHneg1Map (φ ≫ ψ) = tateHneg1Map ψ ∘ₗ tateHneg1Map φ := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x : A.ρ.Coinvariants)
  simp only [LinearMap.comp_apply, coe_tateHneg1Map_apply]
  rw [← ha]
  rfl

end maps

end lowDegrees

section graded

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

noncomputable def tateCohomology (A : Rep.{u} k G) : ℤ → ModuleCat.{u} k
  | (Int.ofNat (n + 1)) => groupCohomology A (n + 1)
  | (Int.ofNat 0) => ModuleCat.of k A.tateH0
  | (Int.negSucc 0) => ModuleCat.of k A.tateHneg1
  | (Int.negSucc (n + 1)) => groupHomology A (n + 1)

lemma tateCohomology_ofNat_succ (A : Rep.{u} k G) (n : ℕ) : A.tateCohomology (n + 1 : ℕ) = groupCohomology A (n + 1) := rfl
lemma tateCohomology_zero (A : Rep.{u} k G) : A.tateCohomology 0 = ModuleCat.of k A.tateH0 := rfl
lemma tateCohomology_neg_one (A : Rep.{u} k G) : A.tateCohomology (-1) = ModuleCat.of k A.tateHneg1 := rfl
lemma tateCohomology_negSucc_succ (A : Rep.{u} k G) (n : ℕ) :
    A.tateCohomology (Int.negSucc (n + 1)) = groupHomology A (n + 1) := rfl

end graded

end Rep
