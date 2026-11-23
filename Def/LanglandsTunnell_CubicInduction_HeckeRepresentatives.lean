import Def.LanglandsTunnell_CubicInduction_Structure
import Instance.LanglandsTunnell_CubicInduction_HeckeRepresentatives
import Structure.LanglandsTunnell_CubicInduction_HeckeRepresentatives

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField Measure

noncomputable section

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives

noncomputable def digit (v : HeightOneSpectrum (𝓞 ℚ)) (d : Fin (Ideal.absNorm v.asIdeal)) : v.adicCompletion ℚ :=
  ((d : ℕ) : v.adicCompletion ℚ)

noncomputable def heckeGen1Reps (v : HeightOneSpectrum (𝓞 ℚ)) {α : Type} (dig : α → v.adicCompletion ℚ) :
    (α × α) ⊕ α ⊕ Unit → LocalGL3 v :=
  Sum.elim (fun ab => upperUnipotent3 (dig ab.1) 0 (dig ab.2) * twoRowPointLocal v 1 0)
    (Sum.elim (fun c => upperUnipotent3 0 (dig c) 0 * twoRowPointLocal v 0 1)
      fun _ => centralGen v * (heckeGen2 v)⁻¹)

noncomputable def heckeGen2Reps (v : HeightOneSpectrum (𝓞 ℚ)) {α : Type} (dig : α → v.adicCompletion ℚ) :
    (α × α) ⊕ α ⊕ Unit → LocalGL3 v :=
  Sum.elim (fun bc => upperUnipotent3 0 (dig bc.2) (dig bc.1) * twoRowPointLocal v 1 1)
    (Sum.elim (fun a => upperUnipotent3 (dig a) 0 0 * (twoRowPointLocal v 1 0 * (centralGen v * (heckeGen2 v)⁻¹)))
      fun _ => twoRowPointLocal v 0 1 * (centralGen v * (heckeGen2 v)⁻¹))

noncomputable def repIndexEquiv (p : ℕ) : (Fin p × Fin p) ⊕ Fin p ⊕ Unit ≃ Fin (p ^ 2 + p + 1) :=
  Fintype.equivFinOfCardEq
    (by simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]; ring)

noncomputable def heckeGen1RepsAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fin (Ideal.absNorm v.asIdeal ^ 2 + Ideal.absNorm v.asIdeal + 1) → LocalGL3 v :=
  heckeGen1Reps v (digit v) ∘ (repIndexEquiv (Ideal.absNorm v.asIdeal)).symm

noncomputable def heckeGen2RepsAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fin (Ideal.absNorm v.asIdeal ^ 2 + Ideal.absNorm v.asIdeal + 1) → LocalGL3 v :=
  heckeGen2Reps v (digit v) ∘ (repIndexEquiv (Ideal.absNorm v.asIdeal)).symm

end LanglandsTunnell.CubicInduction.HeckeRepresentatives

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Hermite


section ExplicitMatrices

variable {A : Type*} [CommRing A]

private noncomputable def diagUnits3 (a b c : Aˣ) : GL (Fin 3) A where
  val := Matrix.diagonal ![(a : A), b, c]
  inv := Matrix.diagonal ![((a⁻¹ : Aˣ) : A), ((b⁻¹ : Aˣ) : A), ((c⁻¹ : Aˣ) : A)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private noncomputable def centralUnit3 (u : Aˣ) : GL (Fin 3) A := diagUnits3 u u u

private noncomputable def slotDiag (π : Aˣ) : Fin 3 → GL (Fin 3) A := ![diagUnits3 π 1 1, diagUnits3 1 π 1,
    diagUnits3 1 1 π]

private noncomputable def slotDiag2 (π : Aˣ) : Fin 3 → GL (Fin 3) A := ![diagUnits3 π π 1, diagUnits3 π 1 π,
    diagUnits3 1 π π]

private noncomputable def longWeyl3 : GL (Fin 3) A where
  val := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  inv := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private noncomputable def swap01 : GL (Fin 3) A where
  val := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
  inv := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private noncomputable def invTranspose3 : GL (Fin 3) A →* GL (Fin 3) A where
  toFun x :=
    { val := (x.inv)ᵀ
      inv := (x.val)ᵀ
      val_inv := by rw [← Matrix.transpose_mul, x.val_inv, Matrix.transpose_one]
      inv_val := by rw [← Matrix.transpose_mul, x.inv_val, Matrix.transpose_one] }
  map_one' := Units.ext (by
    show ((1 : Matrix (Fin 3) (Fin 3) A))ᵀ = (1 : Matrix (Fin 3) (Fin 3) A)
    exact Matrix.transpose_one)
  map_mul' x y := Units.ext (by
    show ((x * y).inv)ᵀ = (x.inv)ᵀ * (y.inv)ᵀ
    show (y.inv * x.inv)ᵀ = (x.inv)ᵀ * (y.inv)ᵀ
    rw [Matrix.transpose_mul])

private noncomputable def theta3 : GL (Fin 3) A →* GL (Fin 3) A :=
  (MulAut.conj (longWeyl3 : GL (Fin 3) A)).toMonoidHom.comp invTranspose3

end ExplicitMatrices


section DiagonalContinuity

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in

end DiagonalContinuity

section Integral

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

private noncomputable def integralGL3 (R K : Type*) [CommRing R] [Field K] [Algebra R K] : Subgroup (GL (Fin 3) K) :=
  (Matrix.GeneralLinearGroup.map (n := Fin 3) (algebraMap R K)).range

variable (hinj : Function.Injective (algebraMap R K))
include hinj

end Integral

section Gen1

open LanglandsTunnell.CubicInduction HeckeIntegralSeam HeckePair

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]


private noncomputable abbrev Gen1Index (κ : Type) : Type := (κ × κ) ⊕ (κ ⊕ Unit)

private noncomputable def slotOf {κ : Type} : Gen1Index κ → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

private noncomputable def gen1Unip {κ : Type} (ℓ : κ → R) : Gen1Index κ → GL (Fin 3) K
  | Sum.inl (a, b) => upperUnipotent3 (algebraMap R K (ℓ a)) 0 (algebraMap R K (ℓ b))
  | Sum.inr (Sum.inl c) => upperUnipotent3 0 (algebraMap R K (ℓ c)) 0
  | Sum.inr (Sum.inr _) => upperUnipotent3 0 0 0

private noncomputable def gen1Reps (π : Kˣ) {κ : Type} (ℓ : κ → R) (i : Gen1Index κ) : GL (Fin 3) K :=
  gen1Unip ℓ i * slotDiag π (slotOf i)

variable (π : Kˣ) {κ : Type} (ℓ : κ → R)

variable {π ℓ}


end Gen1

section Gen2

open LanglandsTunnell.CubicInduction HeckeIntegralSeam HeckePair

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

private noncomputable def gen2Reps (π : Kˣ) {κ : Type} (ℓ : κ → R) (i : Gen1Index κ) : GL (Fin 3) K :=
  theta3 (gen1Reps π ℓ i) * centralUnit3 π

end Gen2

section Bridge

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Matrix.AdelicLevel Measure Matrix
open LanglandsTunnell.CubicInduction HeckeIntegralSeam

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def uniformizerInt : v.adicCompletionIntegers ℚ :=
  ⟨varpi v, by
    show Valued.v (varpi v) ≤ 1
    have h : Valued.v (varpi v) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit ℚ v
    rw [h]
    exact (WithZero.exp_le_exp (a := (-1 : ℤ)) (b := 0)).mpr (by norm_num)⟩

end Bridge

section Residues

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Measure.AdelicHaar Measure Matrix
open Matrix.AdelicLevel LanglandsTunnell.CubicInduction HeckeIntegralSeam

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def ResidueIndex : Type := 𝓞 ℚ ⧸ v.asIdeal

private noncomputable def residueRep (c : ResidueIndex v) : v.adicCompletionIntegers ℚ :=
  algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) (Quotient.out c)

end Residues

end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Hermite


namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Membership

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable {α : Type}

variable {v}

variable (v)

private noncomputable def selfInverse (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (hM : M * M = 1) :
    LocalGL3 v :=
  ⟨M, M, hM, hM⟩

private noncomputable def swap12 : LocalGL3 v :=
  selfInverse v !![0, 1, 0; 1, 0, 0; 0, 0, 1] (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

private noncomputable def swap13 : LocalGL3 v :=
  selfInverse v !![0, 0, 1; 0, 1, 0; 1, 0, 0] (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

private noncomputable def swap23 : LocalGL3 v :=
  selfInverse v !![1, 0, 0; 0, 0, 1; 0, 1, 0] (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

private noncomputable def diagGL3 (a b c : (v.adicCompletion ℚ)ˣ) : LocalGL3 v where
  val := Matrix.diagonal ![(a : v.adicCompletion ℚ), b, c]
  inv := Matrix.diagonal ![((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), (b⁻¹ : (v.adicCompletion ℚ)ˣ),
    (c⁻¹ : (v.adicCompletion ℚ)ˣ)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private noncomputable def deltaUnit : (v.adicCompletion ℚ)ˣ := ratPrimeUnit v * (AdelicLevel.uniformizerUnit ℚ v)⁻¹

end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Membership

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Injectivity

private noncomputable abbrev Mat3 (v : HeightOneSpectrum (𝓞 ℚ)) : Type :=
  Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)

variable {v : HeightOneSpectrum (𝓞 ℚ)} {α : Type}


section Injective

variable {U : Subgroup (LocalGL3 v)}
variable (hU : ∀ k ∈ U, ∀ i j, Valued.v ((k : Mat3 v) i j) ≤ 1)
variable (dig : α → v.adicCompletion ℚ) (hsep : ∀ a b : α, a ≠ b → Valued.v (dig a - dig b) = 1)
variable (hP : Valued.v (ratPrimeUnit v : v.adicCompletion ℚ) < 1) {ϖ : v.adicCompletion ℚ} (hϖ : Valued.v ϖ < 1)
variable (hcorner :
  ((centralGen v * (heckeGen2 v)⁻¹ : LocalGL3 v) : Mat3 v) = !![1, 0, 0; 0, 1, 0; 0, 0, ϖ])

end Injective

end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Injectivity


end
