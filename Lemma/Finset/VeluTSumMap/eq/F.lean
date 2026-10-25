import Mathlib
import sympy.Basic
import Lemma.WeierstrassCurve.Velu
open WeierstrassCurve


/--
map of  along a ring homomorphism.
-/
private lemma map_veluT
  [CommRing R] [CommRing A]
  (W : WeierstrassCurve R) (f : R →+* A) (x y : R) :
-- imply
  (W.map f).veluT (f x) (f y) = f (W.veluT x y) := by
-- proof
  simp [WeierstrassCurve.veluT_eq, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, map_ofNat, map_add, map_mul, map_pow]

private lemma map_veluGx
  [CommRing R] [CommRing A]
  (W : WeierstrassCurve R) (f : R →+* A) (x y : R) :
  (W.map f).veluGx (f x) (f y) = f (W.veluGx x y) := by
  simp [WeierstrassCurve.veluGx, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, map_ofNat, map_add, map_mul, map_sub, map_pow]

private lemma map_veluGy
  [CommRing R] [CommRing A]
  (W : WeierstrassCurve R) (f : R →+* A) (x y : R) :
  (W.map f).veluGy (f x) (f y) = f (W.veluGy x y) := by
  simp [WeierstrassCurve.veluGy, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_ofNat, map_add, map_mul, map_neg]

private lemma map_veluU
  [CommRing R] [CommRing A]
  (W : WeierstrassCurve R) (f : R →+* A) (x y : R) :
  (W.map f).veluU (f x) (f y) = f (W.veluU x y) := by
  simp [WeierstrassCurve.veluU, map_veluGy]

private lemma map_veluW
  [CommRing R] [CommRing A]
  (W : WeierstrassCurve R) (f : R →+* A) (x y : R) :
  (W.map f).veluW (f x) (f y) = f (W.veluW x y) := by
  simp [WeierstrassCurve.veluW, map_veluU, map_veluT]

private lemma map_veluWSum
  [CommRing R] [CommRing A]
  (W : WeierstrassCurve R) (f : R →+* A) (S : Finset (R × R))
  (hf : Function.Injective f) :
  (W.map f).veluWSum (S.map ⟨Prod.map f f, hf.prodMap hf⟩) = f (W.veluWSum S) := by
  rw [WeierstrassCurve.veluWSum, WeierstrassCurve.veluWSum, Finset.sum_map, map_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simp [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluW]

/--
[VeluTSumMap.eq.F] Finset sum of  commutes with ring-hom image.
-/
@[path]
private lemma main
  [CommRing R] [CommRing A]
  {W : WeierstrassCurve R}
  {f : R →+* A}
  {S : Finset (R × R)}
-- given
  (hf : Function.Injective f) :
-- imply
  (W.map f).veluTSum (S.map ⟨Prod.map f f, hf.prodMap hf⟩) = f (W.veluTSum S) := by
-- proof
  rw [WeierstrassCurve.veluTSum, WeierstrassCurve.veluTSum, Finset.sum_map, map_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simp [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT]


-- created on 2026-10-24
