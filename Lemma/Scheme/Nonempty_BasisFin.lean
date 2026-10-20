import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk.lean)
-/
@[path]
private lemma main
    {k : Type u} [Field k] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n p] (y : Y) :
    let _ : Algebra k (Y.presheaf.stalk y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom.toAlgebra
    Nonempty (Module.Basis (Fin n) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄k])) := by
  classical
  let algk : Algebra k (Y.presheaf.stalk y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom.toAlgebra
  obtain ⟨U, hU, V, hV, hyV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := p) y
  have hUtop : U = ⊤ := by
    ext z
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have hz : z = p y := Subsingleton.elim _ _
    rw [hz]; exact e hyV
  subst hUtop
  set A := Γ(Y, V) with hA
  let algA : Algebra k Γ(Y, V) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ V e).hom.toAlgebra
  let algVs : Algebra Γ(Y, V) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hyV⟩
  let _ : IsScalarTower k Γ(Y, V) (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq fun r => by
    show ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom r =
      (Y.presheaf.germ V y hyV).hom (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ V e).hom r)
    rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    rfl
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(Y, V) := by
    have h := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_left_isIso
      (Scheme.ΓSpecIso (.of k)).inv (p.appLE ⊤ V e) |>.mpr hf
    rw [← CommRingCat.hom_comp] at h
    exact h
  let _ := hstd
  let _ : Algebra.IsStandardSmooth k Γ(Y, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let _ : Nontrivial Γ(Y, V) := (algebraMap Γ(Y, V) (Y.presheaf.stalk y)).domain_nontrivial
  have hrank : Module.rank Γ(Y, V) Ω[Γ(Y, V)⁄k] = n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  let _ : Module.Finite Γ(Y, V) Ω[Γ(Y, V)⁄k] := Module.finite_of_rank_eq_nat hrank
  let bA : Module.Basis (Fin n) Γ(Y, V) Ω[Γ(Y, V)⁄k] :=
    Module.finBasisOfFinrankEq _ _ (Module.finrank_eq_of_rank_eq hrank)
  let _ := hV.isLocalization_stalk ⟨y, hyV⟩
  exact ⟨bA.ofIsLocalizedModule (Y.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl
    (KaehlerDifferential.map k k Γ(Y, V) (Y.presheaf.stalk y))⟩

-- created on 2026-10-20
