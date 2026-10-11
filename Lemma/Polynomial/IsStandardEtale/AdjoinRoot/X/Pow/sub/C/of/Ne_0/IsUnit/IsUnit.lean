import sympy.Basic
import Mathlib

open Polynomial

/--
[AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit.lean)
(Kummer `IsStandardEtale` half)
-/

private noncomputable def sepPair
  [CommRing R]
  (f : R[X]) (hf : f.Monic) (hsep : f.Separable) : StandardEtalePair R where
  f := f
  monic_f := hf
  g := 1
  cond := by
    obtain ⟨a, b, hab⟩ := hsep
    exact ⟨b, a, 0, by rw [pow_zero, ← hab]; ring⟩

private lemma sepPair_f
  [CommRing R]
  (f : R[X]) (hf : f.Monic) (hsep : f.Separable) :
  (sepPair f hf hsep).f = f :=
  rfl

private lemma sepPair_g
  [CommRing R]
  (f : R[X]) (hf : f.Monic) (hsep : f.Separable) :
  (sepPair f hf hsep).g = 1 :=
  rfl

private noncomputable def sepPresentation
  [CommRing R]
  (f : R[X]) (hf : f.Monic) (hsep : f.Separable) :
  StandardEtalePresentation R (AdjoinRoot f) where
  __ := sepPair f hf hsep
  x := AdjoinRoot.root f
  hasMap := ⟨by rw [sepPair_f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self],
    by rw [sepPair_g, map_one]; exact isUnit_one⟩
  lift_bijective := by
    have hX : (sepPair f hf hsep).HasMap (AdjoinRoot.root f) :=
      ⟨by rw [sepPair_f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self],
       by rw [sepPair_g, map_one]; exact isUnit_one⟩
    set P := sepPair f hf hsep
    have hzero : Polynomial.aeval P.X f = 0 := by
      have := P.hasMap_X.1
      rwa [sepPair_f] at this
    let ψ : AlgHom R (AdjoinRoot f) P.Ring :=
      AdjoinRoot.liftAlgHom f (Algebra.ofId R P.Ring) P.X hzero
    have hroot : ψ (AdjoinRoot.root f) = P.X :=
      AdjoinRoot.liftAlgHom_root f (Algebra.ofId R P.Ring) P.X hzero
    refine (AlgEquiv.ofAlgHom (P.lift _ hX) ψ ?_ ?_).bijective
    ·
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, hroot, StandardEtalePair.lift_X, AlgHom.id_apply]
    ·
      apply StandardEtalePair.hom_ext
      rw [AlgHom.comp_apply, StandardEtalePair.lift_X, hroot, AlgHom.id_apply]

@[path]
private lemma main
  [CommRing R]
-- given
  (n : ℕ)
  (u : R)
  (hn0 : n ≠ 0)
  (hn : IsUnit (n : R))
  (hu : IsUnit u) :
-- imply
  Algebra.IsStandardEtale R (AdjoinRoot (X ^ n - C u : R[X])) := by
-- proof
  refine ⟨⟨sepPresentation (X ^ n - C u) (monic_X_pow_sub_C u hn0) ?_⟩⟩
  simpa using separable_X_pow_sub_C_unit (n := n) hu.unit hn


-- created on 2026-10-10
