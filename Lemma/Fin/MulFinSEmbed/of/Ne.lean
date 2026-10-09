import Mathlib
import sympy.Basic

open IsDedekindDomain RestrictedProduct NumberField
open scoped Classical AdeleRing

namespace AdelicDockPort

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

noncomputable def finAdeleEval (v : HeightOneSpectrum R) :
  FiniteAdeleRing R K →+* v.adicCompletion K :=
  RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum R => w.adicCompletion K) v

@[simp]
lemma finAdeleEval_apply (v : HeightOneSpectrum R) (a : FiniteAdeleRing R K) :
  finAdeleEval R K v a = a v :=
  RestrictedProduct.evalRingHom_apply _ _ _

lemma matrix_eq_of_forall_mapMatrix_finAdeleEval_eq
  {M N : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}
  (h : ∀ w : HeightOneSpectrum R,
    (finAdeleEval R K w).mapMatrix M = (finAdeleEval R K w).mapMatrix N) :
  M = N := by
  ext i j w
  have hw := congrFun (congrFun (h w) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply] at hw
  rw [hw]

variable (v : HeightOneSpectrum R)

noncomputable def splice (a : FiniteAdeleRing R K) (t : v.adicCompletion K) :
  FiniteAdeleRing R K :=
  ⟨Function.update (⇑a) v t, (Filter.eventually_cofinite_ne v).mp (a.2.mono fun w hw hne => by
    rw [Function.update_of_ne hne]
    apply hw)⟩

@[simp]
lemma splice_apply_self (a : FiniteAdeleRing R K) (t : v.adicCompletion K) :
  splice R K v a t v = t := by
  show Function.update (⇑a) v t v = t
  simp

lemma splice_apply_of_ne (a : FiniteAdeleRing R K) (t : v.adicCompletion K)
  {w : HeightOneSpectrum R} (hw : w ≠ v) :
  splice R K v a t w = a w := by
  show Function.update (⇑a) v t w = a w
  simp [Function.update_of_ne hw]

noncomputable def localMat (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
  Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.of fun i j =>
    splice R K v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j) (g i j)

lemma localMat_apply_self (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
  (i j : Fin 2) :
  localMat R K v g i j v = g i j := by
  simp [localMat]

lemma localMat_apply_of_ne (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
  (i j : Fin 2) {w : HeightOneSpectrum R} (hw : w ≠ v) :
  localMat R K v g i j w =
    (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
  simp only [localMat, Matrix.of_apply, splice_apply_of_ne R K v _ _ hw]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

lemma mapMatrix_localMat_self (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
  (finAdeleEval R K v).mapMatrix (localMat R K v g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply, localMat_apply_self]

lemma mapMatrix_localMat_of_ne (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
  {w : HeightOneSpectrum R} (hw : w ≠ v) :
  (finAdeleEval R K w).mapMatrix (localMat R K v g) = 1 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply,
    localMat_apply_of_ne R K v g i j hw]

lemma localMat_one : localMat R K v 1 = 1 := by
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  if hw : w = v then
    subst hw
    rw [mapMatrix_localMat_self, map_one]
  else
    rw [mapMatrix_localMat_of_ne R K v _ hw, map_one]

lemma localMat_mul (g h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
  localMat R K v (g * h) = localMat R K v g * localMat R K v h := by
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  if hw : w = v then
    subst hw
    rw [map_mul, mapMatrix_localMat_self, mapMatrix_localMat_self, mapMatrix_localMat_self]
  else
    rw [map_mul, mapMatrix_localMat_of_ne R K v _ hw, mapMatrix_localMat_of_ne R K v _ hw,
      mapMatrix_localMat_of_ne R K v _ hw, mul_one]

noncomputable def localEmbed :
  GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (FiniteAdeleRing R K) where
  toFun g :=
    { val := localMat R K v g
      inv := localMat R K v ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix _ _ _)
      val_inv := by rw [← localMat_mul, Units.mul_inv, localMat_one]
      inv_val := by rw [← localMat_mul, Units.inv_mul, localMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; apply localMat_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; apply localMat_mul)

@[simp]
lemma coe_localEmbed (g : GL (Fin 2) (v.adicCompletion K)) :
  ((localEmbed R K v g : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _) =
    localMat R K v g :=
  rfl

noncomputable def adeleArch : AdeleRing R K →+* InfiniteAdeleRing K where
  toFun := Prod.fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma adeleArch_apply (a : AdeleRing R K) : adeleArch R K a = a.1 := rfl

noncomputable def adeleFin : AdeleRing R K →+* FiniteAdeleRing R K where
  toFun := Prod.snd
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma adeleFin_apply (a : AdeleRing R K) : adeleFin R K a = a.2 := rfl

lemma matrix_eq_of_mapMatrix_arch_fin_eq
  {M N : Matrix (Fin 2) (Fin 2) (AdeleRing R K)}
  (h₁ : (adeleArch R K).mapMatrix M = (adeleArch R K).mapMatrix N)
  (h₂ : (adeleFin R K).mapMatrix M = (adeleFin R K).mapMatrix N) :
  M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply,
    adeleFin_apply] at hw₁ hw₂
  apply Prod.ext hw₁ hw₂

noncomputable def finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
  Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  fun i j => ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, g i j)

lemma mapMatrix_arch_finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
  (adeleArch R K).mapMatrix (finMat R K g) = 1 := by
  ext i j
  rfl

lemma mapMatrix_fin_finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
  (adeleFin R K).mapMatrix (finMat R K g) = g := by
  ext i j
  rfl

lemma finMat_one : finMat R K 1 = 1 :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K (by rw [mapMatrix_arch_finMat, map_one])
    (by rw [mapMatrix_fin_finMat, map_one])

lemma finMat_mul (g h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
  finMat R K (g * h) = finMat R K g * finMat R K h :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K
    (by rw [map_mul, mapMatrix_arch_finMat, mapMatrix_arch_finMat, mapMatrix_arch_finMat, mul_one])
    (by rw [map_mul, mapMatrix_fin_finMat, mapMatrix_fin_finMat, mapMatrix_fin_finMat])

noncomputable def finEmbed :
  GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (AdeleRing R K) where
  toFun g :=
    { val := finMat R K g
      inv := finMat R K ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)
      val_inv := by rw [← finMat_mul, Units.mul_inv, finMat_one]
      inv_val := by rw [← finMat_mul, Units.inv_mul, finMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; apply finMat_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; apply finMat_mul)

end AdelicDockPort

open AdelicDockPort

/--
[AdelicDock_finEmbed_localEmbed_comm_of_ne](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdelicDock_finEmbed_localEmbed_comm_of_ne.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {v w : HeightOneSpectrum R}
  {x : GL (Fin 2) (v.adicCompletion K)}
  {y : GL (Fin 2) (w.adicCompletion K)}
-- given
  (hvw : v ≠ w) :
-- imply
  finEmbed R K (localEmbed R K v x) * finEmbed R K (localEmbed R K w y) =
    finEmbed R K (localEmbed R K w y) * finEmbed R K (localEmbed R K v x) := by
-- proof
  rw [← map_mul (finEmbed R K), ← map_mul (finEmbed R K)]
  congr 1
  refine Units.ext ?_
  simp only [Units.val_mul, coe_localEmbed]
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun u => ?_
  rw [map_mul, map_mul]
  if huv : u = v then
    subst huv
    rw [mapMatrix_localMat_self, mapMatrix_localMat_of_ne R K w _ hvw, mul_one, one_mul]
  else if huw : u = w then
    subst huw
    rw [mapMatrix_localMat_self, mapMatrix_localMat_of_ne R K v _ huv, mul_one, one_mul]
  else
    rw [mapMatrix_localMat_of_ne R K v _ huv, mapMatrix_localMat_of_ne R K w _ huw]


-- created on 2026-10-09
