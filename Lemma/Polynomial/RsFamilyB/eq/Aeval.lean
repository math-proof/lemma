import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.EllipticCurve_RubinSilverbergFamily
open Polynomial RubinSilverberg


private lemma map_kleinH
  {R S : Type*}
  [CommRing R]
  [CommRing S]
  {Φ : Type*}
  [FunLike Φ R S]
  [RingHomClass Φ R S]
  (f : Φ) (u : R) : f (kleinH u) = kleinH (f u) := by
  simp [kleinH, map_sub, map_add, map_mul, map_pow, map_ofNat]

private lemma map_kleinT
  {R S : Type*}
  [CommRing R]
  [CommRing S]
  {Φ : Type*}
  [FunLike Φ R S]
  [RingHomClass Φ R S]
  (f : Φ) (u : R) : f (kleinT u) = kleinT (f u) := by
  simp [kleinT, map_sub, map_add, map_mul, map_pow, map_ofNat]

private lemma map_kleinHHom
  {R S : Type*}
  [CommRing R]
  [CommRing S]
  {Φ : Type*}
  [FunLike Φ R S]
  [RingHomClass Φ R S]
  (f : Φ) (n d : R) : f (kleinHHom n d) = kleinHHom (f n) (f d) := by
  simp [kleinHHom, map_sub, map_add, map_mul, map_pow, map_ofNat]

private lemma map_kleinTHom
  {R S : Type*}
  [CommRing R]
  [CommRing S]
  {Φ : Type*}
  [FunLike Φ R S]
  [RingHomClass Φ R S]
  (f : Φ) (n d : R) : f (kleinTHom n d) = kleinTHom (f n) (f d) := by
  simp [kleinTHom, map_sub, map_add, map_mul, map_pow, map_ofNat]

private lemma map_rsBeta
  {K L : Type*}
  [Field K]
  [Field L]
  {Φ : Type*}
  [FunLike Φ K L]
  [RingHomClass Φ K L]
  (f : Φ) (u : K) : f (rsBeta u) = rsBeta (f u) := by
  simp [rsBeta, map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat, map_kleinT]

private lemma map_rsGamma
  {K L : Type*}
  [Field K]
  [Field L]
  {Φ : Type*}
  [FunLike Φ K L]
  [RingHomClass Φ K L]
  (f : Φ) (u : K) : f (rsGamma u) = rsGamma (f u) := by
  simp [rsGamma, map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat, map_kleinT]

private lemma rsFamilyA_eq_aeval
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (a u₀ l : K) (x : F) :
  rsFamilyA (algebraMap K F a) (algebraMap K F u₀) (algebraMap K F l) x =
    aeval x (C (a / kleinH u₀) *
      kleinHHom (C (rsBeta u₀ + l * u₀) * X + C u₀) (C (rsGamma u₀ + l) * X + 1)) := by
  rw [map_mul, map_kleinHHom, aeval_C]
  simp only [map_add, map_mul, aeval_C, aeval_X, map_one, rsFamilyA, rsNum, rsDen, ← map_rsBeta,
    ← map_rsGamma, ← map_kleinH, map_div₀]
  ring

private lemma rsFamilyB_eq_aeval
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (b u₀ l : K) (x : F) :
  rsFamilyB (algebraMap K F b) (algebraMap K F u₀) (algebraMap K F l) x =
    aeval x (C (b / kleinT u₀) *
      kleinTHom (C (rsBeta u₀ + l * u₀) * X + C u₀) (C (rsGamma u₀ + l) * X + 1)) := by
  rw [map_mul, map_kleinTHom, aeval_C]
  simp only [map_add, map_mul, aeval_C, aeval_X, map_one, rsFamilyB, rsNum, rsDen, ← map_rsBeta,
    ← map_rsGamma, ← map_kleinT, map_div₀]
  ring

private lemma map_eq_rsFamilyA_poly
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  [Infinite F]
  {a l : K} {u₀ : F} {pa : K[X]}
  (h : ∀ t : F, rsFamilyA (algebraMap K F a) u₀ (algebraMap K F l) t = (pa.map (algebraMap K F)).eval t) :
  pa.map (algebraMap K F) = C (algebraMap K F a / kleinH u₀) *
    kleinHHom (C (rsBeta u₀ + algebraMap K F l * u₀) * X + C u₀) (C (rsGamma u₀ + algebraMap K F l) * X + 1) := by
  apply Polynomial.funext
  intro t
  rw [← h t, ← coe_aeval_eq_eval, ← rsFamilyA_eq_aeval (K := F) (F := F)]
  simp

private lemma map_eq_rsFamilyB_poly
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  [Infinite F]
  {b l : K} {u₀ : F} {pb : K[X]}
  (h : ∀ t : F, rsFamilyB (algebraMap K F b) u₀ (algebraMap K F l) t = (pb.map (algebraMap K F)).eval t) :
  pb.map (algebraMap K F) = C (algebraMap K F b / kleinT u₀) *
    kleinTHom (C (rsBeta u₀ + algebraMap K F l * u₀) * X + C u₀) (C (rsGamma u₀ + algebraMap K F l) * X + 1) := by
  apply Polynomial.funext
  intro t
  rw [← h t, ← coe_aeval_eq_eval, ← rsFamilyB_eq_aeval (K := F) (F := F)]
  simp

open RubinSilverberg in
/--
[RubinSilverberg_rsFamilyB_eq_aeval](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RubinSilverberg_rsFamilyB_eq_aeval.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {b u₀ l : K}
  {x : F} :
-- imply
  rsFamilyB (algebraMap K F b) (algebraMap K F u₀) (algebraMap K F l) x = Polynomial.aeval x (Polynomial.C (b / kleinT u₀) * kleinTHom (Polynomial.C (rsBeta u₀ + l * u₀) * Polynomial.X + Polynomial.C u₀) (Polynomial.C (rsGamma u₀ + l) * Polynomial.X + 1)) :=
-- proof
  rsFamilyB_eq_aeval b u₀ l x


-- created on 2026-10-23
