import Mathlib
import sympy.Basic
import Def.AlgebraicGeometry_CoherentBaseChange
open scoped TensorProduct
open CoherentBaseChange
open CoherentBaseChange.TwoTermComplex


noncomputable def rk
  {R : Type u}
  [CommRing R]
  (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
  (K : Type w)
  [Field K]
  [Algebra R K]
  : ℕ := Module.finrank K (LinearMap.range (G.d.baseChange K))

private lemma h0_add_rk
  {R : Type u}
  [CommRing R]
  (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
  (K : Type w)
  [Field K]
  [Algebra R K] :
  Module.finrank K (LinearMap.ker (G.d.baseChange K)) + rk G K =
    Module.finrank K (K ⊗[R] G.C0) := by
  have h := LinearMap.finrank_range_add_finrank_ker (G.d.baseChange K)
  unfold rk; omega

private lemma rk_add_h1
  {R : Type u}
  [CommRing R]
  (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
  (K : Type w)
  [Field K]
  [Algebra R K] :
  rk G K + Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) =
    Module.finrank K (K ⊗[R] G.C1) := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (G.d.baseChange K))
  unfold rk; omega

private lemma helper_main
  {R : Type u}
  [CommRing R]
  (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
  (K : Type w)
  [Field K]
  [Algebra R K] :
  (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
    Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  have h0 := h0_add_rk G K
  have h1 := rk_add_h1 G K
  rw [Module.finrank_baseChange] at h0 h1
  show _ = (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ)
  have h0' : (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) + (rk G K : ℤ) =
      (Module.finrank R G.C0 : ℤ) := by exact_mod_cast h0
  have h1' : (rk G K : ℤ) + (Module.finrank K ((K ⊗[R] G.C1) ⧸
      LinearMap.range (G.d.baseChange K)) : ℤ) = (Module.finrank R G.C1 : ℤ) := by exact_mod_cast h1
  omega
/--
[CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {K : Type w} [Field K] [Algebra R K]
  {G : CoherentBaseChange.TwoTermComplex.{u, v} R} :
-- imply
  (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi :=
-- proof
  helper_main G K


-- created on 2026-10-24
