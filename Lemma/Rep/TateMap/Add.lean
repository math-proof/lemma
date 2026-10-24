import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GroupCohomology_TateCohomology
import Lemma.Definitions.Def_GroupCohomology_TateSeam
import Lemma.Definitions.Def_GroupCohomology_TateShiftMaps
import Lemma.Int.P2MUtil

open CategoryTheory Rep

/--
[Rep_tateMap_add](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_tateMap_add.lean)
-/

private lemma  cochainsMap_f_apply
    {k G : Type u}
    [CommRing k]
    [Group G]
    {A B : Rep.{u} k G}
    (χ : A ⟶ B) (i : ℕ) (x : (Fin i → G) → A) (σ : Fin i → G) :
    ((groupCohomology.cochainsMap (MonoidHom.id G) χ).f i).hom x σ = χ.hom (x σ) := by
  rw [groupCohomology.cochainsMap_f_hom]
  rfl

private lemma  cochainsMap_add
    {k G : Type u}
    [CommRing k]
    [Group G]
    {A B : Rep.{u} k G}
    (φ ψ : A ⟶ B) :
    groupCohomology.cochainsMap (MonoidHom.id G) (φ + ψ)
      = groupCohomology.cochainsMap (MonoidHom.id G) φ + groupCohomology.cochainsMap (MonoidHom.id G) ψ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ModuleCat.hom_ext (LinearMap.ext fun x => funext fun σ => ?_)
  rw [HomologicalComplex.add_f_apply, ModuleCat.hom_add, LinearMap.add_apply, Pi.add_apply,
    cochainsMap_f_apply, cochainsMap_f_apply, cochainsMap_f_apply]
  rfl

private lemma  cohomologyMap_add
    {k G : Type u}
    [CommRing k]
    [Group G]
    {A B : Rep.{u} k G}
    (φ ψ : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (φ + ψ) n
      = groupCohomology.map (MonoidHom.id G) φ n + groupCohomology.map (MonoidHom.id G) ψ n := by
  change HomologicalComplex.homologyMap _ n = HomologicalComplex.homologyMap _ n + HomologicalComplex.homologyMap _ n
  rw [cochainsMap_add, HomologicalComplex.homologyMap_add]
  rfl

private lemma  chainsMap_f_apply
    {k G : Type u}
    [CommRing k]
    [Group G]
    {A B : Rep.{u} k G}
    (χ : A ⟶ B) (i : ℕ) (x : (Fin i → G) →₀ A) (σ : Fin i → G) :
    ((groupHomology.chainsMap (MonoidHom.id G) χ).f i).hom x σ = χ.hom (x σ) := by
  rw [groupHomology.chainsMap_f_hom, LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
  change χ.hom (Finsupp.mapDomain (fun x => ⇑(MonoidHom.id G) ∘ x) x σ) = _
  rw [show (fun x : Fin i → G => ⇑(MonoidHom.id G) ∘ x) = id from rfl, Finsupp.mapDomain_id]

private lemma  chainsMap_add
    {k G : Type u}
    [CommRing k]
    [Group G]
    {A B : Rep.{u} k G}
    (φ ψ : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) (φ + ψ)
      = groupHomology.chainsMap (MonoidHom.id G) φ + groupHomology.chainsMap (MonoidHom.id G) ψ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ModuleCat.hom_ext (LinearMap.ext fun x => Finsupp.ext fun σ => ?_)
  rw [HomologicalComplex.add_f_apply, ModuleCat.hom_add, LinearMap.add_apply, Finsupp.add_apply,
    chainsMap_f_apply, chainsMap_f_apply, chainsMap_f_apply]
  rfl

private theorem _root_.P2mS26TAdd.homologyMap_add
    {k G : Type u}
    [CommRing k]
    [Group G]
    {A B : Rep.{u} k G}
    (φ ψ : A ⟶ B) (n : ℕ) :
    groupHomology.map (MonoidHom.id G) (φ + ψ) n
      = groupHomology.map (MonoidHom.id G) φ n + groupHomology.map (MonoidHom.id G) ψ n := by
  change HomologicalComplex.homologyMap _ n = HomologicalComplex.homologyMap _ n + HomologicalComplex.homologyMap _ n
  rw [chainsMap_add, HomologicalComplex.homologyMap_add]
  rfl

p2m_export "P2mS26TAdd" "homologyMap_add"

private lemma  tateH0Map_add
    {k G : Type u}
    [CommRing k]
    [Group G]
    {A B : Rep.{u} k G}
    [Fintype G]
    (φ ψ : A ⟶ B) :
    ModuleCat.ofHom (Rep.tateH0Map (φ + ψ)) = ModuleCat.ofHom (Rep.tateH0Map φ) + ModuleCat.ofHom (Rep.tateH0Map ψ) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
  change Submodule.Quotient.mk (Rep.invariantsMap (φ + ψ) a)
    = Submodule.Quotient.mk (Rep.invariantsMap φ a) + Submodule.Quotient.mk (Rep.invariantsMap ψ a)
  rw [← Submodule.Quotient.mk_add]
  exact congrArg _ (Subtype.ext rfl)

private lemma  tateHneg1Map_add
    {k G : Type u}
    [CommRing k]
    [Group G]
    {A B : Rep.{u} k G}
    [Fintype G]
    (φ ψ : A ⟶ B) :
    ModuleCat.ofHom (Rep.tateHneg1Map (φ + ψ)) = ModuleCat.ofHom (Rep.tateHneg1Map φ) + ModuleCat.ofHom (Rep.tateHneg1Map ψ) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  rw [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
  apply Subtype.ext
  rw [Submodule.coe_add, Rep.coe_tateHneg1Map_apply, Rep.coe_tateHneg1Map_apply, Rep.coe_tateHneg1Map_apply]
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x : A.ρ.Coinvariants)
  rw [← ha]
  change Representation.Coinvariants.mk B.ρ ((φ + ψ).hom a)
    = Representation.Coinvariants.mk B.ρ (φ.hom a) + Representation.Coinvariants.mk B.ρ (ψ.hom a)
  rw [← map_add]
  rfl


@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G] [Fintype G]
  {A B : Rep.{u} k G}
  {φ ψ : A ⟶ B}
  {n : ℤ} :
-- imply
  Rep.tateMap (φ + ψ) n = Rep.tateMap φ n + Rep.tateMap ψ n := by
-- proof
  rcases n with (_ | m) | (_ | m)
  · exact tateH0Map_add φ ψ
  · exact cohomologyMap_add φ ψ (m + 1)
  · exact tateHneg1Map_add φ ψ
  · exact homologyMap_add φ ψ (m + 1)


-- created on 2026-10-23
