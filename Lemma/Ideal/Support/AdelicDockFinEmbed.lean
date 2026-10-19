import Mathlib
import Lemma.AdicCompletion.IsCompact.LocalLevelOne
import Lemma.Fin.MulFinSEmbed.of.Ne

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum


/-! FLT AdelicDock / AdelicLevel ports for finEmbed–localEmbed level-one lemmas. -/

/--
Port of `AdelicLevel.idealBound_eq_one_of_not_dvd` from
[Def_NumberField_AdelicLevel](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_NumberField_AdelicLevel.lean).
-/
theorem AdelicLevel.idealBound_eq_one_of_not_dvd
  {R : Type*} [CommRing R] [IsDedekindDomain R] {N : Ideal R} (hN : N ≠ ⊥)
  {v : HeightOneSpectrum R} (hv : ¬ v.asIdeal ∣ N) : AdelicLevel.idealBound R N v = 1 := by
  classical
  rw [AdelicLevel.idealBound_of_ne_bot hN]
  have h0 : (Associates.mk v.asIdeal).count (Associates.mk N).factors = 0 := by
    by_contra h
    apply hv
    apply (Associates.count_ne_zero_iff_dvd (show N ≠ 0 from hN) v.irreducible).mp
    apply h
  rw [h0]
  simp

def integralSubgroup (R K : Type*) [CommRing R] [Field K] [Algebra R K] :
  Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range

section Projections

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

noncomputable def glArch : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (AdelicDockPort.adeleArch R K)

noncomputable def glFin : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.GeneralLinearGroup.map (AdelicDockPort.adeleFin R K)

noncomputable def finComponent (v : HeightOneSpectrum R) :
  GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map (AdelicDockPort.finAdeleEval R K v)

@[simp]
theorem glArch_apply (g : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
  (glArch R K g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j =
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).1 :=
  rfl

@[simp]
theorem glFin_apply (g : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
  (glFin R K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j =
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 :=
  rfl

@[simp]
theorem finComponent_apply (v : HeightOneSpectrum R) (g : GL (Fin 2) (FiniteAdeleRing R K))
  (i j : Fin 2) :
  (finComponent R K v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
    (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j v :=
  rfl

noncomputable abbrev localEmbed (v : HeightOneSpectrum R) :=
  AdelicDockPort.localEmbed R K v

noncomputable abbrev finEmbed := AdelicDockPort.finEmbed R K

theorem glArch_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) :
  glArch R K (finEmbed R K g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glArch_apply, Units.val_one]
  rfl

theorem glFin_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) :
  glFin R K (finEmbed R K g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_apply]
  rfl

theorem finComponent_localEmbed_self (v : HeightOneSpectrum R)
  (g : GL (Fin 2) (v.adicCompletion K)) :
  finComponent R K v (localEmbed R K v g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [finComponent_apply, AdelicDockPort.coe_localEmbed, AdelicDockPort.localMat_apply_self]

theorem finComponent_localEmbed_of_ne (v : HeightOneSpectrum R)
  (g : GL (Fin 2) (v.adicCompletion K)) {w : HeightOneSpectrum R} (hw : w ≠ v) :
  finComponent R K w (localEmbed R K v g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [finComponent_apply, AdelicDockPort.coe_localEmbed,
    AdelicDockPort.localMat_apply_of_ne R K v _ i j hw, Units.val_one]

end Projections

noncomputable def finiteAdelicGL2Subgroup (K : Type*) [Field K] [NumberField K] :
  Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
  MonoidHom.ker (glArch (𝓞 K) K)

section FiniteLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def integralFiniteAdeles : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, x v ∈ v.adicCompletionIntegers K}

def idealBall (N : Ideal R) : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, Valued.v (x v) ≤ AdelicLevel.idealBound R N v}

variable {R K}

theorem coe_one_apply (v : HeightOneSpectrum R) : (1 : FiniteAdeleRing R K) v = 1 :=
  rfl

theorem coe_sub_apply (x y : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
  (x - y) v = x v - y v :=
  rfl

theorem one_mem_integralFiniteAdeles : (1 : FiniteAdeleRing R K) ∈ integralFiniteAdeles R K :=
  fun _ => one_mem _

theorem zero_mem_integralFiniteAdeles : (0 : FiniteAdeleRing R K) ∈ integralFiniteAdeles R K :=
  fun _ => zero_mem _

theorem add_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K}
  (hx : x ∈ integralFiniteAdeles R K) (hy : y ∈ integralFiniteAdeles R K) :
  x + y ∈ integralFiniteAdeles R K :=
  fun v => add_mem (hx v) (hy v)

theorem mul_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K}
  (hx : x ∈ integralFiniteAdeles R K) (hy : y ∈ integralFiniteAdeles R K) :
  x * y ∈ integralFiniteAdeles R K :=
  fun v => mul_mem (hx v) (hy v)

theorem zero_mem_idealBall (N : Ideal R) : (0 : FiniteAdeleRing R K) ∈ idealBall R K N :=
  fun v => by
    rw [show (0 : FiniteAdeleRing R K) v = 0 from rfl, map_zero]
    apply zero_le

theorem valued_apply_le_one {x : FiniteAdeleRing R K} (hx : x ∈ integralFiniteAdeles R K)
  (v : HeightOneSpectrum R) : Valued.v (x v) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hx v)

theorem add_mem_idealBall {N : Ideal R} {x y : FiniteAdeleRing R K}
  (hx : x ∈ idealBall R K N) (hy : y ∈ idealBall R K N) : x + y ∈ idealBall R K N :=
  fun v => (Valuation.map_add _ _ _).trans (max_le (hx v) (hy v))

theorem mul_mem_idealBall_left {N : Ideal R} {x y : FiniteAdeleRing R K}
  (hx : x ∈ integralFiniteAdeles R K) (hy : y ∈ idealBall R K N) :
  x * y ∈ idealBall R K N := fun v => by
  change Valued.v (x v * y v) ≤ AdelicLevel.idealBound R N v
  rw [map_mul]
  calc
    Valued.v (x v) * Valued.v (y v) ≤ 1 * AdelicLevel.idealBound R N v :=
      mul_le_mul' (valued_apply_le_one hx v) (hy v)
    _ = AdelicLevel.idealBound R N v := one_mul _

theorem mul_mem_idealBall_right {N : Ideal R} {x y : FiniteAdeleRing R K}
  (hx : x ∈ idealBall R K N) (hy : y ∈ integralFiniteAdeles R K) :
  x * y ∈ idealBall R K N := by
  rw [mul_comm]
  apply mul_mem_idealBall_left hy hx

structure IsLevelZeroMatrix (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Prop where
  integral : ∀ i j, m i j ∈ integralFiniteAdeles R K
  lowerLeft : m 1 0 ∈ idealBall R K N

structure IsLevelOneMatrix (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Prop extends IsLevelZeroMatrix N m where
  lowerRight : m 1 1 - 1 ∈ idealBall R K N

namespace IsLevelZeroMatrix

variable {N : Ideal R}

protected theorem one : IsLevelZeroMatrix N (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) where
  integral i j := by
    rw [Matrix.one_apply]
    split_ifs
    · apply one_mem_integralFiniteAdeles
    · apply zero_mem_integralFiniteAdeles
  lowerLeft := by
    rw [Matrix.one_apply_ne (by decide)]
    apply zero_mem_idealBall

variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}

protected theorem mul (hm : IsLevelZeroMatrix N m) (hm' : IsLevelZeroMatrix N m') :
  IsLevelZeroMatrix N (m * m') where
  integral i j := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    apply add_mem_integralFiniteAdeles
    · apply mul_mem_integralFiniteAdeles (hm.integral i 0) (hm'.integral 0 j)
    · apply mul_mem_integralFiniteAdeles (hm.integral i 1) (hm'.integral 1 j)
  lowerLeft := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    apply add_mem_idealBall
    · apply mul_mem_idealBall_right hm.lowerLeft (hm'.integral 0 0)
    · apply mul_mem_idealBall_left (hm.integral 1 1) hm'.lowerLeft

end IsLevelZeroMatrix

namespace IsLevelOneMatrix

variable {N : Ideal R}

protected theorem one : IsLevelOneMatrix N (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) where
  toIsLevelZeroMatrix := .one
  lowerRight := by
    rw [Matrix.one_apply_eq, sub_self]
    apply zero_mem_idealBall

variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}

protected theorem mul (hm : IsLevelOneMatrix N m) (hm' : IsLevelOneMatrix N m') :
  IsLevelOneMatrix N (m * m') where
  toIsLevelZeroMatrix := hm.toIsLevelZeroMatrix.mul hm'.toIsLevelZeroMatrix
  lowerRight := by
    have h : (m * m') 1 1 - 1 =
        m 1 0 * m' 0 1 + ((m 1 1 - 1) * m' 1 1 + (m' 1 1 - 1)) := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [h]
    apply add_mem_idealBall
    · apply mul_mem_idealBall_right hm.lowerLeft (hm'.integral 0 1)
    · apply add_mem_idealBall
      · apply mul_mem_idealBall_right hm.lowerRight (hm'.integral 1 1)
      · apply hm'.lowerRight

end IsLevelOneMatrix

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (N : Ideal R)

noncomputable def finiteLevelOne : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | IsLevelOneMatrix (R := R) (K := K) N
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelOneMatrix (R := R) (K := K) N
      ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))}
  one_mem' := ⟨by
      rw [Units.val_one]
      apply IsLevelOneMatrix.one, by
      rw [inv_one, Units.val_one]
      apply IsLevelOneMatrix.one⟩
  mul_mem' {a b} ha hb := ⟨by
      rw [Units.val_mul]
      apply ha.1.mul hb.1, by
      rw [mul_inv_rev, Units.val_mul]
      apply hb.2.mul ha.2⟩
  inv_mem' {a} ha := ⟨ha.2, by
      rw [inv_inv]
      apply ha.1⟩

variable {R K N}

theorem mem_finiteLevelOne_iff {g : GL (Fin 2) (FiniteAdeleRing R K)} :
  g ∈ finiteLevelOne R K N ↔
    IsLevelOneMatrix (R := R) (K := K) N
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelOneMatrix (R := R) (K := K) N
      ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :=
  Iff.rfl

variable (R K N)

noncomputable def levelOne : Subgroup (GL (Fin 2) (AdeleRing R K)) :=
  (finiteLevelOne R K N).comap (glFin R K)

variable {R K N}

theorem mem_levelOne_iff {g : GL (Fin 2) (AdeleRing R K)} :
  g ∈ levelOne R K N ↔ glFin R K g ∈ finiteLevelOne R K N :=
  Iff.rfl

end FiniteLevel

/--
Port of the private `mem_inf_of_components` argument from
[S_AdelicDock_finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdelicDock_finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup.lean).
-/
theorem mem_inf_of_components
  (F : Type*) [Field F] [NumberField F] {N : Ideal (𝓞 F)}
  {h : GL (Fin 2) (AdeleRing (𝓞 F) F)} (harch : glArch (𝓞 F) F h = 1)
  (hfin : ∀ w : HeightOneSpectrum (𝓞 F),
    finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ AdelicDock.localLevelOne (𝓞 F) F w N) :
  h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    have hlocal : ∀ w, AdelicDock.IsLocalLevelOne (𝓞 F) F w N
          (finComponent (𝓞 F) F w (glFin (𝓞 F) F h) : Matrix (Fin 2) (Fin 2) _) ∧
        AdelicDock.IsLocalLevelOne (𝓞 F) F w N
          ((finComponent (𝓞 F) F w (glFin (𝓞 F) F h))⁻¹ : GL (Fin 2) _) := by
      intro w
      apply (AdelicDock.mem_localLevelOne_iff (𝓞 F) F w N
        (finComponent (𝓞 F) F w (glFin (𝓞 F) F h))).mp
      apply hfin
    constructor
    · refine ⟨⟨fun i j w => (hlocal w).1.integral i j, fun w => (hlocal w).1.lowerLeft⟩, fun w => ?_⟩
      rw [coe_sub_apply, coe_one_apply]
      apply (hlocal w).1.lowerRight
    · refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · have := (hlocal w).2.integral i j
        rwa [← map_inv] at this
      · have := (hlocal w).2.lowerLeft
        rwa [← map_inv] at this
      · rw [coe_sub_apply, coe_one_apply]
        have := (hlocal w).2.lowerRight
        rwa [← map_inv] at this
  · change h ∈ MonoidHom.ker (glArch (𝓞 F) F)
    rw [MonoidHom.mem_ker]
    apply harch
