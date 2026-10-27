import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Flat_of_forall_isClosed_flat_stalk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Flat_of_forall_isClosed_flat_stalk.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of R)) [CompactSpace ↥X]
-- given
  (h : ∀ x : ↥X, IsClosed ({x} : Set ↥X) →
    let _ : Algebra R ↑(X.presheaf.stalk x) :=
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom).toAlgebra
    Module.Flat R ↑(X.presheaf.stalk x)) :
-- imply
  Flat f := by
-- proof
  classical
  apply AlgebraicGeometry.Flat.of_stalkMap
  intro x'
  obtain ⟨x, hxmem, hxcl⟩ := (isClosed_closure (s := ({x'} : Set ↥X))).exists_closed_singleton
    ⟨x', subset_closure (Set.mem_singleton x')⟩
  have hsp : x' ⤳ x := specializes_iff_mem_closure.mpr hxmem
  let algx : Algebra R ↑(X.presheaf.stalk x) :=
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom).toAlgebra
  let algx' : Algebra R ↑(X.presheaf.stalk x') :=
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x' trivial).hom).toAlgebra
  have hflx : Module.Flat R ↑(X.presheaf.stalk x) := h x hxcl
  have hflx' : Module.Flat R ↑(X.presheaf.stalk x') := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hx'U : x' ∈ U := hsp.mem_open U.2 hxU
    let aU : Algebra ↑(X.presheaf.obj (Opposite.op U)) ↑(X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
    let aU' : Algebra ↑(X.presheaf.obj (Opposite.op U)) ↑(X.presheaf.stalk x') := X.presheaf.algebra_section_stalk ⟨x', hx'U⟩
    let hloc' : IsLocalization.AtPrime ↑(X.presheaf.stalk x') (hU.primeIdealOf ⟨x', hx'U⟩).asIdeal :=
      hU.isLocalization_stalk ⟨x', hx'U⟩
    let hloc : IsLocalization.AtPrime ↑(X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
      hU.isLocalization_stalk ⟨x, hxU⟩
    let asp : Algebra ↑(X.presheaf.stalk x) ↑(X.presheaf.stalk x') := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
    let _ : IsScalarTower ↑(X.presheaf.obj (Opposite.op U)) ↑(X.presheaf.stalk x) ↑(X.presheaf.stalk x') := by
      refine IsScalarTower.of_algebraMap_eq (fun s => ?_)
      show X.presheaf.germ U x' hx'U s = (X.presheaf.stalkSpecializes hsp).hom (X.presheaf.germ U x hxU s)
      exact (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxU hsp s).symm
    have h1 : Module.Flat ↑(X.presheaf.obj (Opposite.op U)) ↑(X.presheaf.stalk x') :=
      IsLocalization.flat _ (hU.primeIdealOf ⟨x', hx'U⟩).asIdeal.primeCompl
    have h2 : Module.Flat ↑(X.presheaf.stalk x) ↑(X.presheaf.stalk x') :=
      (Module.flat_iff_of_isLocalization ↑(X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
        ↑(X.presheaf.stalk x')).mpr h1
    let _ : IsScalarTower R ↑(X.presheaf.stalk x) ↑(X.presheaf.stalk x') := by
      refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
      show (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x' trivial).hom) r =
        (X.presheaf.stalkSpecializes hsp).hom
          ((((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom) r)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      exact (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf (U := ⊤) (show x ∈ (⊤ : X.Opens) from trivial) hsp _).symm
    exact Module.Flat.trans R ↑(X.presheaf.stalk x) ↑(X.presheaf.stalk x')
  let aS : Algebra R ↑((Spec (CommRingCat.of R)).presheaf.stalk (f.base x')) :=
    (AlgebraicGeometry.StructureSheaf.toStalk R (f.base x')).hom.toAlgebra
  let _ : IsLocalization.AtPrime ↑((Spec (CommRingCat.of R)).presheaf.stalk (f.base x')) (f.base x').asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk R (f.base x')
  let asm : Algebra ↑((Spec (CommRingCat.of R)).presheaf.stalk (f.base x')) ↑(X.presheaf.stalk x') :=
    (f.stalkMap x').hom.toAlgebra
  let _ : IsScalarTower R ↑((Spec (CommRingCat.of R)).presheaf.stalk (f.base x')) ↑(X.presheaf.stalk x') := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    show (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x' trivial).hom) r =
      (f.stalkMap x').hom ((AlgebraicGeometry.StructureSheaf.toStalk R (f.base x')).hom r)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, AlgebraicGeometry.StructureSheaf.toStalk,
      Scheme.ΓSpecIso_inv]
    exact (Scheme.Hom.germ_stalkMap_apply f ⊤ x' trivial _).symm
  have hst : Module.Flat ↑((Spec (CommRingCat.of R)).presheaf.stalk (f.base x')) ↑(X.presheaf.stalk x') :=
    (Module.flat_iff_of_isLocalization ↑((Spec (CommRingCat.of R)).presheaf.stalk (f.base x'))
      (f.base x').asIdeal.primeCompl ↑(X.presheaf.stalk x')).mpr hflx'
  refine hst


-- created on 2026-10-20
