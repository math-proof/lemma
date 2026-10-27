import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] {Y : (Scheme : Type (u + 1))} (p : Y ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n p] (y : Y) :
  -- imply
  let _ : Algebra k (Y.presheaf.stalk y) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom.toAlgebra
  Nonempty (Module.Basis (Fin n) (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k]) := by
  -- proof
  classical
  let algk : Algebra k (Y.presheaf.stalk y) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom.toAlgebra
  obtain ⟨U, hU, V, hV, hyV, e, hf⟩ := SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := p) y
  have hUtop : U = ⊤ := by
    ext z
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have hz : z = p y := Subsingleton.elim _ _
    rw [hz]
    apply e hyV
  subst hUtop
  let algA : Algebra k (Y.presheaf.obj (Opposite.op V)) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e).hom.toAlgebra
  let algVs : Algebra (Y.presheaf.obj (Opposite.op V)) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hyV⟩
  let _ : IsScalarTower k (Y.presheaf.obj (Opposite.op V)) (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq fun r => by
    show ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom r = (Y.presheaf.germ V y hyV).hom (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e).hom r)
    rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    rfl
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension n k (Y.presheaf.obj (Opposite.op V)) := by
    have h := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv (p.appLE ⊤ V e) |>.mpr hf
    rw [← CommRingCat.hom_comp] at h
    apply h
  let _ := hstd
  let _ : Algebra.IsStandardSmooth k (Y.presheaf.obj (Opposite.op V)) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let _ : Nontrivial (Y.presheaf.obj (Opposite.op V)) := (algebraMap (Y.presheaf.obj (Opposite.op V)) (Y.presheaf.stalk y)).domain_nontrivial
  have hrank : Module.rank (Y.presheaf.obj (Opposite.op V)) Ω[(Y.presheaf.obj (Opposite.op V))⁄k] = n := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  let _ : Module.Finite (Y.presheaf.obj (Opposite.op V)) Ω[(Y.presheaf.obj (Opposite.op V))⁄k] := Module.finite_of_rank_eq_nat hrank
  let bA : Module.Basis (Fin n) (Y.presheaf.obj (Opposite.op V)) Ω[(Y.presheaf.obj (Opposite.op V))⁄k] := Module.finBasisOfFinrankEq _ _ (Module.finrank_eq_of_rank_eq hrank)
  let _ := hV.isLocalization_stalk ⟨y, hyV⟩
  refine ⟨bA.ofIsLocalizedModule (Y.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl (KaehlerDifferential.map k k (Y.presheaf.obj (Opposite.op V)) (Y.presheaf.stalk y))⟩


-- created on 2026-10-20
