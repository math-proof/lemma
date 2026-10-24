import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Lemma.Definitions.Def_AdelicDock_LocalEmbedding

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Embeddings

variable (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem matrixFin_ext {M N : Matrix ι ι (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R,
      (AdelicLevel.finAdeleEval R K w).mapMatrix M = (AdelicLevel.finAdeleEval R K w).mapMatrix N) :
    M = N := by
  ext i j w : 2
  have hw := congrFun (congrFun (h w) i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply] using hw

theorem matrixAdele_ext {M N : Matrix ι ι (AdeleRing R K)}
    (h₁ : (AdelicLevel.adeleArch R K).mapMatrix M = (AdelicLevel.adeleArch R K).mapMatrix N)
    (h₂ : (AdelicLevel.adeleFin R K).mapMatrix M = (AdelicLevel.adeleFin R K).mapMatrix N) :
    M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply,
    AdelicLevel.adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

variable (v : HeightOneSpectrum R)

def localMatN (g : Matrix ι ι (v.adicCompletion K)) : Matrix ι ι (FiniteAdeleRing R K) :=
  Matrix.of fun i j => AdelicDock.splice R K v ((1 : Matrix ι ι (FiniteAdeleRing R K)) i j) (g i j)

omit [Fintype ι] in
theorem localMatN_apply_self (g : Matrix ι ι (v.adicCompletion K)) (i j : ι) :
    localMatN ι R K v g i j v = g i j := by
  simp [localMatN]

omit [Fintype ι] in
theorem localMatN_apply_of_ne (g : Matrix ι ι (v.adicCompletion K)) (i j : ι)
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    localMatN ι R K v g i j w = (1 : Matrix ι ι (w.adicCompletion K)) i j := by
  simp only [localMatN, Matrix.of_apply, AdelicDock.splice_apply_of_ne R K v _ _ hw]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem mapMatrix_localMatN_self (g : Matrix ι ι (v.adicCompletion K)) :
    (AdelicLevel.finAdeleEval R K v).mapMatrix (localMatN ι R K v g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_self]

theorem mapMatrix_localMatN_of_ne (g : Matrix ι ι (v.adicCompletion K))
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    (AdelicLevel.finAdeleEval R K w).mapMatrix (localMatN ι R K v g) = 1 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_of_ne ι R K v g i j hw]

theorem localMatN_one : localMatN ι R K v 1 = 1 := by
  refine matrixFin_ext ι R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [mapMatrix_localMatN_self, map_one]
  · rw [mapMatrix_localMatN_of_ne ι R K v _ hw, map_one]

theorem localMatN_mul (g h : Matrix ι ι (v.adicCompletion K)) :
    localMatN ι R K v (g * h) = localMatN ι R K v g * localMatN ι R K v h := by
  refine matrixFin_ext ι R K fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [map_mul, mapMatrix_localMatN_self, mapMatrix_localMatN_self, mapMatrix_localMatN_self]
  · rw [map_mul, mapMatrix_localMatN_of_ne ι R K v _ hw, mapMatrix_localMatN_of_ne ι R K v _ hw,
      mapMatrix_localMatN_of_ne ι R K v _ hw, mul_one]

def localEmbedN : GL ι (v.adicCompletion K) →* GL ι (FiniteAdeleRing R K) where
  toFun g :=
    { val := localMatN ι R K v g
      inv := localMatN ι R K v ((g⁻¹ : GL ι (v.adicCompletion K)) : Matrix _ _ _)
      val_inv := by rw [← localMatN_mul, Units.mul_inv, localMatN_one]
      inv_val := by rw [← localMatN_mul, Units.inv_mul, localMatN_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact localMatN_one ι R K v)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact localMatN_mul ι R K v _ _)

def finMatN (g : Matrix ι ι (FiniteAdeleRing R K)) : Matrix ι ι (AdeleRing R K) :=
  Matrix.of fun i j => (((1 : Matrix ι ι (InfiniteAdeleRing K)) i j, g i j) : AdeleRing R K)

theorem mapMatrix_arch_finMatN (g : Matrix ι ι (FiniteAdeleRing R K)) :
    (AdelicLevel.adeleArch R K).mapMatrix (finMatN ι R K g) = 1 := by
  ext i j
  simp [finMatN, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_finMatN (g : Matrix ι ι (FiniteAdeleRing R K)) :
    (AdelicLevel.adeleFin R K).mapMatrix (finMatN ι R K g) = g := by
  ext i j
  simp [finMatN, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

theorem finMatN_one : finMatN ι R K 1 = 1 :=
  matrixAdele_ext ι R K (by rw [mapMatrix_arch_finMatN, map_one])
    (by rw [mapMatrix_fin_finMatN, map_one])

theorem finMatN_mul (g h : Matrix ι ι (FiniteAdeleRing R K)) :
    finMatN ι R K (g * h) = finMatN ι R K g * finMatN ι R K h :=
  matrixAdele_ext ι R K
    (by rw [map_mul, mapMatrix_arch_finMatN, mapMatrix_arch_finMatN, mapMatrix_arch_finMatN, mul_one])
    (by rw [map_mul, mapMatrix_fin_finMatN, mapMatrix_fin_finMatN, mapMatrix_fin_finMatN])

def finEmbedN : GL ι (FiniteAdeleRing R K) →* GL ι (AdeleRing R K) where
  toFun g :=
    { val := finMatN ι R K g
      inv := finMatN ι R K ((g⁻¹ : GL ι (FiniteAdeleRing R K)) : Matrix _ _ _)
      val_inv := by rw [← finMatN_mul, Units.mul_inv, finMatN_one]
      inv_val := by rw [← finMatN_mul, Units.inv_mul, finMatN_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact finMatN_one ι R K)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact finMatN_mul ι R K _ _)

def localToAdelicN : GL ι (v.adicCompletion K) →* GL ι (AdeleRing R K) :=
  (finEmbedN ι R K).comp (localEmbedN ι R K v)

end Embeddings

section LocalThree

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev localToAdelic3 : LocalGL3 v →* AdelicGL 3 (𝓞 ℚ) ℚ :=
  localToAdelicN (Fin 3) (𝓞 ℚ) ℚ v

def converseCongruenceSet3 (a : ℕ) : Set (LocalGL3 v) :=
  {k | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1) ≤ WithZero.exp (-(a : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0) ≤ WithZero.exp (-(a : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1) ≤ WithZero.exp (-(2 * (a : ℤ)))}

theorem one_mem_converseCongruenceSet3 (a : ℕ) : (1 : LocalGL3 v) ∈ converseCongruenceSet3 v a := by
  refine ⟨Subgroup.one_mem _, ?_, ?_, ?_⟩
  · rw [Units.val_one, Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le
  · rw [Units.val_one, Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le
  · rw [Units.val_one, Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le

def parabolicCongruenceSet3 (a : ℕ) : Set (LocalGL3 v) :=
  {g | ∃ p k : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
    (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧ k ∈ converseCongruenceSet3 v a ∧
    g = p * k}

def IsCongruenceEquivariantAt (a : ℕ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (W : LocalGL3 v → ℂ) : Prop :=
  ∀ k ∈ converseCongruenceSet3 v a, ∀ u : (v.adicCompletion ℚ)ˣ,
    (u : v.adicCompletion ℚ) = (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 →
      ∀ g, W (g * k) = ((χ u : ℂˣ) : ℂ) * W g

def HasVanishingUnipotentIntegralAt (W : LocalGL3 v → ℂ) : Prop :=
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  ∀ g : LocalGL3 v,
    (∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)}, W (g * upperUnipotent3 0 x 0)
      ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) = 0

def HasVanishingUnipotentIntegralAlong (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)},
        W (g * localToAdelic3 v (upperUnipotent3 0 x 0))
      ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) = 0

def IsCongruenceEquivariantAlong (a : ℕ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∀ k ∈ converseCongruenceSet3 v a, ∀ u : (v.adicCompletion ℚ)ˣ,
    (u : v.adicCompletion ℚ) = (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 →
      ∀ g, W (g * localToAdelic3 v k) = ((χ u : ℂˣ) : ℂ) * W g

end LocalThree

section Global

structure AutomorphyDatum31 (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ) where

  form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

  continuous : Continuous form
  automorphic : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
    form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = form g
  central : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
    form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * form g
  moderateGrowth : IsModerateGrowth3 ℚ form
  equivariant : ∀ v ∈ S, IsCongruenceEquivariantAlong v (a v) (TateGlobal.localChar ω v) form
  whittaker_eq : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      whittaker3 pins ψ form g = W g
  cuspidalP21 : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ parabolicCongruenceSet3 v (a v)) →
      (letI := pins.nS; ∫ x, ∫ y, form (radicalP21 ![x, y] * g) ∂pins.ν ∂pins.ν) = 0
  heckeInvariant : ∀ p, p ∉ S →
    IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) form
  hecke1 : ∀ p, p ∉ S →
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) form (lam1 p)
  hecke2 : ∀ p, p ∉ S →
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) form (lam2 p)

def AutomorphyDatum31.zero (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ) :
    AutomorphyDatum31 pins ψ S a ω 0 lam1 lam2 where
  form := 0
  continuous := continuous_const
  automorphic := fun _ _ => rfl
  central := fun _ _ => by simp
  moderateGrowth := isModerateGrowth3_zero ℚ
  equivariant := fun _ _ _ _ _ _ _ => by simp
  whittaker_eq := fun _ _ => by simp only [whittaker3, Pi.zero_apply, zero_mul, MeasureTheory.integral_zero]
  cuspidalP21 := fun _ _ => by simp
  heckeInvariant := fun _ _ _ _ _ => rfl
  hecke1 := fun p _ => isCosetEigenfunction_zero _ _ (lam1 p)
  hecke2 := fun p _ => isCosetEigenfunction_zero _ _ (lam2 p)

end Global

end LanglandsTunnell.CubicInduction

end

#check @LanglandsTunnell.CubicInduction.localToAdelic3
#check @LanglandsTunnell.CubicInduction.converseCongruenceSet3
#check @LanglandsTunnell.CubicInduction.IsCongruenceEquivariantAt
#check @LanglandsTunnell.CubicInduction.HasVanishingUnipotentIntegralAt
#check @LanglandsTunnell.CubicInduction.AutomorphyDatum31
#check @LanglandsTunnell.CubicInduction.HasVanishingUnipotentIntegralAlong
#check @LanglandsTunnell.CubicInduction.IsCongruenceEquivariantAlong
#print axioms LanglandsTunnell.CubicInduction.localToAdelicN
#print axioms LanglandsTunnell.CubicInduction.one_mem_converseCongruenceSet3
#print axioms LanglandsTunnell.CubicInduction.AutomorphyDatum31.zero
