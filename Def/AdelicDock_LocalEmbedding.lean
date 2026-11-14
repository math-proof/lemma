import Lemma.Matrix.AdelicLevel
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AdelicDock

section Generic

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (v : HeightOneSpectrum R)

open scoped Classical in
def splice (a : FiniteAdeleRing R K) (t : v.adicCompletion K) : FiniteAdeleRing R K :=
  ⟨Function.update (⇑a) v t, (Filter.eventually_cofinite_ne v).mp (a.2.mono fun w hw hne => by
    rw [Function.update_of_ne hne]; exact hw)⟩

def localMat (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.of fun i j => splice R K v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j) (g i j)

open scoped Classical in
def localEmbed : GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (FiniteAdeleRing R K) :=
  have splice_apply_self (a : FiniteAdeleRing R K) (t : v.adicCompletion K) :
      splice R K v a t v = t := by
    show Function.update (⇑a) v t v = t
    simp
  have splice_apply_of_ne (a : FiniteAdeleRing R K) (t : v.adicCompletion K) {w : HeightOneSpectrum R}
      (hw : w ≠ v) : splice R K v a t w = a w := by
    show Function.update (⇑a) v t w = a w
    simp [Function.update_of_ne hw]
  have localMat_apply_self (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (i j : Fin 2) :
      localMat R K v g i j v = g i j := by
    simp [localMat, splice_apply_self]
  have localMat_apply_of_ne (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (i j : Fin 2)
      {w : HeightOneSpectrum R} (hw : w ≠ v) :
      localMat R K v g i j w = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
    simp only [localMat, Matrix.of_apply, splice_apply_of_ne _ _ hw]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  have mapMatrix_localMat_self (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
      (AdelicLevel.finAdeleEval R K v).mapMatrix (localMat R K v g) = g := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, localMat_apply_self]
  have mapMatrix_localMat_of_ne (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
      {w : HeightOneSpectrum R} (hw : w ≠ v) :
      (AdelicLevel.finAdeleEval R K w).mapMatrix (localMat R K v g) = 1 := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply,
      localMat_apply_of_ne g i j hw]
  have matrix_eq_of_forall_mapMatrix_finAdeleEval_eq {M N : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}
      (h : ∀ w : HeightOneSpectrum R,
        (AdelicLevel.finAdeleEval R K w).mapMatrix M = (AdelicLevel.finAdeleEval R K w).mapMatrix N) :
      M = N := by
    ext i j w
    have hw := congrFun (congrFun (h w) i) j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply] at hw
    rw [hw]
  have localMat_one : localMat R K v 1 = 1 := by
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [mapMatrix_localMat_self, map_one]
    · rw [mapMatrix_localMat_of_ne _ hw, map_one]
  have localMat_mul (g h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
      localMat R K v (g * h) = localMat R K v g * localMat R K v h := by
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [map_mul, mapMatrix_localMat_self, mapMatrix_localMat_self, mapMatrix_localMat_self]
    · rw [map_mul, mapMatrix_localMat_of_ne _ hw, mapMatrix_localMat_of_ne _ hw,
        mapMatrix_localMat_of_ne _ hw, mul_one]
  { toFun := fun g =>
      { val := localMat R K v g
        inv := localMat R K v ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix _ _ _)
        val_inv := by rw [← localMat_mul, Units.mul_inv, localMat_one]
        inv_val := by rw [← localMat_mul, Units.inv_mul, localMat_one] }
    map_one' := Units.ext (by simp only [Units.val_one]; exact localMat_one)
    map_mul' := fun g h => Units.ext (by simp only [Units.val_mul]; exact localMat_mul _ _) }

def finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j => (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, g i j) : AdeleRing R K)

def finEmbed : GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (AdeleRing R K) :=
  have mapMatrix_arch_finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
      (AdelicLevel.adeleArch R K).mapMatrix (finMat R K g) = 1 := by
    ext i j
    simp [finMat, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]
  have mapMatrix_fin_finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
      (AdelicLevel.adeleFin R K).mapMatrix (finMat R K g) = g := by
    ext i j
    simp [finMat, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]
  have matrix_eq_of_mapMatrix_arch_fin_eq {M N : Matrix (Fin 2) (Fin 2) (AdeleRing R K)}
      (h₁ : (AdelicLevel.adeleArch R K).mapMatrix M = (AdelicLevel.adeleArch R K).mapMatrix N)
      (h₂ : (AdelicLevel.adeleFin R K).mapMatrix M = (AdelicLevel.adeleFin R K).mapMatrix N) :
      M = N := by
    ext i j
    have hw₁ := congrFun (congrFun h₁ i) j
    have hw₂ := congrFun (congrFun h₂ i) j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply,
      AdelicLevel.adeleFin_apply] at hw₁ hw₂
    exact Prod.ext hw₁ hw₂
  have finMat_one : finMat R K 1 = 1 :=
    matrix_eq_of_mapMatrix_arch_fin_eq (by rw [mapMatrix_arch_finMat, map_one])
      (by rw [mapMatrix_fin_finMat, map_one])
  have finMat_mul (g h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
      finMat R K (g * h) = finMat R K g * finMat R K h :=
    matrix_eq_of_mapMatrix_arch_fin_eq
      (by rw [map_mul, mapMatrix_arch_finMat, mapMatrix_arch_finMat, mapMatrix_arch_finMat, mul_one])
      (by rw [map_mul, mapMatrix_fin_finMat, mapMatrix_fin_finMat, mapMatrix_fin_finMat])
  { toFun := fun g =>
      { val := finMat R K g
        inv := finMat R K ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)
        val_inv := by rw [← finMat_mul, Units.mul_inv, finMat_one]
        inv_val := by rw [← finMat_mul, Units.inv_mul, finMat_one] }
    map_one' := Units.ext (by simp only [Units.val_one]; exact finMat_one)
    map_mul' := fun g h => Units.ext (by simp only [Units.val_mul]; exact finMat_mul _ _) }

def localLevelOne (N : Ideal R) : Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  (AdelicLevel.finiteLevelOne R K N).comap (localEmbed R K v)

end Generic

section Rat

variable (p : ℕ) [Fact p.Prime]

def padicPlace : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, Fact.out⟩

def padicRingEquiv : ℚ_[p] ≃+* (padicPlace p).adicCompletion ℚ :=
  (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, Fact.out⟩).toRingEquiv

def padicGL : GL (Fin 2) ℚ_[p] →* GL (Fin 2) ((padicPlace p).adicCompletion ℚ) :=
  Matrix.GeneralLinearGroup.map (padicRingEquiv p).toRingHom

def padicToFinAdelic : GL (Fin 2) ℚ_[p] →* GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  (localEmbed (𝓞 ℚ) ℚ (padicPlace p)).comp (padicGL p)

def padicToAdelic : GL (Fin 2) ℚ_[p] →* GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  (finEmbed (𝓞 ℚ) ℚ).comp (padicToFinAdelic p)

def ratLevel (N : ℕ) : Ideal (𝓞 ℚ) := Ideal.span {(N : 𝓞 ℚ)}

end Rat

end AdelicDock

end
