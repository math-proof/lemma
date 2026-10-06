import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry Opposite

/--
[AlgebraicGeometry_Scheme_Modules_hom_ext_of_isIso_fromTildeGamma](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_hom_ext_of_isIso_fromTildeGamma.lean)
-/
@[main]
private lemma main
  {R : CommRingCat.{u}}
  {M N : (Spec (.of R)).Modules} [IsIso (Scheme.Modules.fromTildeΓ M)]
  {φ ψ : M ⟶ N}
-- given
  (h : ∀ m : Γ(M, ⊤), φ.app ⊤ m = ψ.app ⊤ m) :
-- imply
  φ = ψ := by
-- proof
  have hΓ : (moduleSpecΓFunctor (R := R)).map φ = (moduleSpecΓFunctor (R := R)).map ψ := by
    ext m
    exact h m
  have n1 := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality φ
  have n2 := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality ψ
  simp only [Functor.comp_map, Functor.id_map] at n1 n2
  rw [← cancel_epi (Scheme.Modules.fromTildeΓ M)]
  change (Scheme.Modules.fromTildeΓNatTrans (R := R)).app M ≫ φ =
    (Scheme.Modules.fromTildeΓNatTrans (R := R)).app M ≫ ψ
  refine n1.symm.trans ?_
  rw [hΓ]
  exact n2


-- created on 2026-10-05
