import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Notation.Fun
import Notation.Probability.HasLaw
import Instance.Probability.Process.HiddenMarkovSequence
import Instance.NNReal.Coe
import Def.Probability.ChiSquare
import Lemma.Measure.MapPi_GaussianReal.eq.ProdChiSquareS.of.Gt_1.Gt_1
open MeasureTheory ProbabilityTheory Fun Measure
open scoped NNReal
set_option maxHeartbeats 800000


/--
Joint ANOVA SS laws under H₀ (common mean).

Balanced design: m groups × n i.i.d. observations.
`(S_B / σ², S_W / σ²) ∼[π] (Real.chiSquare (m - 1)).prod (Real.chiSquare (m * (n - 1)))`.

Marginals:
[S_B / σ² ∼ χ²(m - 1)](?module=Random.Distributed_ChiSquared.of.All_And_Distributed_Gaussian.Gt_1.Gt_1.sb),
[S_W / σ² ∼ χ²(m (n - 1))](?module=Random.Distributed_ChiSquared.of.All_And_Distributed_Gaussian.Gt_1.Gt_1.sw).
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {m n : ℕ}
  {y : ℕ ⇀ ℕ ⇀ Ω → ℝ}
  {μ : ℝ} {σ : ℝ⁺}
-- given
  (hm : m > 1)
  (hn : n > 1)
  (h : ∀ (i j : ℕ), y[i][:j] ⟂ᵢ[π]
        ((y[:i, :j] : Ω → Fin i → Fin j → ℝ), y[i][j]) ∧
      y[i][j] ∼[π] gaussianReal μ (σ : NNReal)²) :
-- imply
  (((n : Ω → ℝ) * (∑ i : Fin m, ((∑ j : Fin n, y[i][j]) / (n : Ω → ℝ) - (∑ i : Fin m, ∑ j : Fin n, y[i][j]) / ((m * n : ℕ) : Ω → ℝ)) ^ 2)) / (σ² : Ω → ℝ),
    (∑ i : Fin m, ∑ j : Fin n, (y[i][j] - (∑ k : Fin n, y[i][k]) / (n : Ω → ℝ)) ^ 2) / (σ² : Ω → ℝ)) ∼[π]
    (Real.chiSquare (m - 1)).prod (Real.chiSquare (m * (n - 1))) := by
-- proof
  have h₁' (i j : ℕ) : HasLaw y[i][j] (gaussianReal μ (σ : NNReal)²) π :=
    (h i j).2
  have hrow : ∀ (N i : ℕ), HasLaw (fun ω (j : Fin N) ↦ y[i][j] ω)
      (Measure.pi fun _ : Fin N ↦ gaussianReal μ (σ : NNReal)²) π := by
    intro N
    induction N with
    | zero =>
      intro i
      have heq : (fun ω (j : Fin 0) ↦ y[i][j] ω) =
          fun _ ↦ (isEmptyElim : Fin 0 → ℝ) := by
        funext ω j; apply j.elim0
      rw [heq]
      refine ⟨measurable_const.aemeasurable, ?_⟩
      rw [Measure.map_const, Measure.pi_of_empty, measure_univ, one_smul]
    | succ N ih =>
      intro i
      have hx : (y[i][:N] : Ω → Fin N → ℝ) = fun ω (j : Fin N) ↦ y[i][j] ω := by
        funext ω j; rfl
      have hprefix : HasLaw y[i][:N] (Measure.pi fun _ : Fin N ↦ gaussianReal μ (σ : NNReal)²) π := by
        simpa [hx] using ih i
      have hwithin : (y[i][:N] : Ω → Fin N → ℝ) ⟂ᵢ[π] y[i][N] :=
        (h i N).1.comp measurable_id measurable_snd
      have hprod := hwithin.hasLaw_prod hprefix (h₁' i N)
      have hY : HasLaw (Prod.swap : (Fin N → ℝ) × ℝ → ℝ × (Fin N → ℝ))
        ((gaussianReal μ (σ : NNReal)²).prod (Measure.pi fun _ : Fin N ↦ gaussianReal μ (σ : NNReal)²))
        ((Measure.pi fun _ : Fin N ↦ gaussianReal μ (σ : NNReal)²).prod (gaussianReal μ (σ : NNReal)²)) :=
        ⟨measurable_swap.aemeasurable, Measure.prod_swap⟩
      have hswap : HasLaw (fun ω ↦ (y[i][N] ω, y[i][:N] ω))
        ((gaussianReal μ (σ : NNReal)²).prod (Measure.pi fun _ : Fin N ↦ gaussianReal μ (σ : NNReal)²)) π :=
        hY.fun_comp hprod
      have hmp :=
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (N + 1) ↦ gaussianReal μ (σ : NNReal)²) (Fin.last N)).symm
      have hlaw := hmp.hasLaw.fun_comp hswap
      have hsnoc : (fun ω (j : Fin (N + 1)) ↦ y[i][j] ω) =
          fun ω ↦ Fin.snoc (y[i][:N] ω) (y[i][N] ω) := by
        funext ω j
        refine Fin.lastCases ?_ ?_ j
        ·
          rw [Fin.snoc_last]
          rfl
        ·
          intro k
          rw [Fin.snoc_castSucc, hx]
          rfl
      rw [hsnoc]
      convert hlaw using 1
      funext ω
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last]
      rfl
  have hrows : ∀ M,
      HasLaw (fun ω (i : Fin M) ↦ fun (j : Fin n) ↦ y[i][j] ω)
        (Measure.pi fun _ : Fin M ↦ Measure.pi fun _ : Fin n ↦ gaussianReal μ (σ : NNReal)²) π := by
    intro M
    induction M with
    | zero =>
      have heq : (fun ω (i : Fin 0) ↦ fun (j : Fin n) ↦ y[i][j] ω) =
          fun _ ↦ (isEmptyElim : Fin 0 → Fin n → ℝ) := by
        funext ω i; exact i.elim0
      rw [heq]
      refine ⟨measurable_const.aemeasurable, ?_⟩
      rw [Measure.map_const, Measure.pi_of_empty, measure_univ, one_smul]
    | succ M ih =>
      have hnew := hrow n M
      have hpast := ih
      have hL : (fun ω (j : Fin n) ↦ y[M][j] ω) = (y[M][:n] : Ω → Fin n → ℝ) := by
        funext ω j; rfl
      have hindep : (fun ω (j : Fin n) ↦ y[M][j] ω) ⟂ᵢ[π]
          (fun ω (i : Fin M) ↦ fun (j : Fin n) ↦ y[i][j] ω) := by
        have hb : (y[M][:n] : Ω → Fin n → ℝ) ⟂ᵢ[π]
          (↑y[:M, :n] : Ω → Fin M → Fin n → ℝ) :=
          (h M n).1.comp measurable_id measurable_fst
        have hpast_eq :
          (↑y[:M, :n] : Ω → Fin M → Fin n → ℝ) =
            fun ω (i : Fin M) ↦ fun (j : Fin n) ↦ y[i][j] ω := by
          funext ω i j; rfl
        rwa [hL, ← hpast_eq]
      have hprod := hindep.symm.hasLaw_prod hpast hnew
      have hY : HasLaw
        (Prod.swap :
          (Fin M → Fin n → ℝ) × (Fin n → ℝ) →
            (Fin n → ℝ) × (Fin M → Fin n → ℝ))
          ((Measure.pi fun _ : Fin n ↦ gaussianReal μ (σ : NNReal)²).prod
            (Measure.pi fun _ : Fin M ↦ Measure.pi fun _ : Fin n ↦ gaussianReal μ (σ : NNReal)²))
          ((Measure.pi fun _ : Fin M ↦ Measure.pi fun _ : Fin n ↦ gaussianReal μ (σ : NNReal)²).prod
            (Measure.pi fun _ : Fin n ↦ gaussianReal μ (σ : NNReal)²)) :=
        ⟨measurable_swap.aemeasurable, Measure.prod_swap⟩
      have hswap := hY.fun_comp hprod
      have hmp :=
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (M + 1) ↦ Measure.pi fun _ : Fin n ↦ gaussianReal μ (σ : NNReal)²)
          (Fin.last M)).symm
      have hlaw := hmp.hasLaw.fun_comp hswap
      have hsnoc :
        (fun ω (i : Fin (M + 1)) ↦ fun (j : Fin n) ↦ y[i][j] ω) =
          fun ω ↦ Fin.snoc
            (fun (i : Fin M) ↦ fun (j : Fin n) ↦ y[i][j] ω)
            (fun (j : Fin n) ↦ y[M][j] ω) := by
        funext ω i
        refine Fin.lastCases ?_ ?_ i
        ·
          funext j
          rw [Fin.snoc_last]
          rfl
        ·
          intro k
          funext j
          rw [Fin.snoc_castSucc]
          rfl
      rw [hsnoc]
      convert hlaw using 1
      funext ω
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last]
      rfl
  have hgrid : HasLaw (fun ω (p : Fin m × Fin n) ↦ y[p.1][p.2] ω)
      (Measure.pi fun _ : Fin m × Fin n ↦ gaussianReal μ (σ : NNReal)²) π := by
    have h := hrows m
    have hmp : MeasurePreserving (MeasurableEquiv.curry (Fin m) (Fin n) ℝ).symm
      (Measure.pi fun _ : Fin m ↦ Measure.pi fun _ : Fin n ↦ gaussianReal μ (σ : NNReal)²)
      (Measure.pi fun _ : Fin m × Fin n ↦ gaussianReal μ (σ : NNReal)²) := by
      constructor
      ·
        exact (MeasurableEquiv.curry (Fin m) (Fin n) ℝ).symm.measurable
      ·
        refine (Measure.pi_eq fun t ht => ?_).symm
        have hmeas : Measurable (MeasurableEquiv.curry (Fin m) (Fin n) ℝ).symm :=
          (MeasurableEquiv.curry (Fin m) (Fin n) ℝ).symm.measurable
        rw [Measure.map_apply hmeas (MeasurableSet.univ_pi ht)]
        have hpre :
          (MeasurableEquiv.curry (Fin m) (Fin n) ℝ).symm ⁻¹' (Set.univ.pi t) =
              Set.univ.pi (fun i : Fin m ↦ Set.univ.pi (fun j : Fin n ↦ t (i, j))) := by
          ext rows
          simp [Set.mem_preimage, MeasurableEquiv.coe_curry_symm, Function.uncurry]
        rw [hpre, Measure.pi_pi]
        simp_rw [Measure.pi_pi (fun _ : Fin n ↦ gaussianReal μ (σ : NNReal)²)]
        exact (Fintype.prod_prod_type
          (fun p : Fin m × Fin n ↦ (gaussianReal μ (σ : NNReal)²) (t p))).symm
    have hcomp :
      (fun ω (p : Fin m × Fin n) ↦ y[p.1][p.2] ω) =
        (MeasurableEquiv.curry (Fin m) (Fin n) ℝ).symm ∘
          (fun ω (i : Fin m) ↦ fun (j : Fin n) ↦ y[i][j] ω) := by
      funext ω p; rfl
    rw [hcomp]
    exact hmp.hasLaw.fun_comp h
  have : NeZero (m - 1) := ⟨ne_of_gt (Nat.sub_pos_of_lt hm)⟩
  have : NeZero (m * (n - 1)) :=
    ⟨ne_of_gt (Nat.mul_pos (Nat.zero_lt_of_lt hm) (Nat.sub_pos_of_lt hn))⟩
  have hANOVA :=
    MapPi_GaussianReal.eq.ProdChiSquareS.of.Gt_1.Gt_1 (m := m) (n := n) (μ := μ) (σ := σ)
      hm hn
  let φ : (Fin m × Fin n → ℝ) → ℝ × ℝ := fun z ↦
    let μbar := (∑ p : Fin m × Fin n, z p) / (m * n : ℝ)
    let S_B :=
      (n : ℝ) *
        ∑ i : Fin m,
          ((∑ j : Fin n, z (i, j)) / (n : ℝ) - μbar) ^ 2
    let S_W :=
      ∑ i : Fin m, ∑ j : Fin n,
        (z (i, j) - (∑ k : Fin n, z (i, k)) / (n : ℝ)) ^ 2
    (S_B / (σ : ℝ) ^ 2, S_W / (σ : ℝ) ^ 2)
  have hφ_meas : AEMeasurable φ
    (Measure.pi fun _ : Fin m × Fin n ↦ gaussianReal μ (σ : NNReal)²) := by
    fun_prop
  have hφ : HasLaw φ
    ((Real.chiSquare (m - 1)).prod (Real.chiSquare (m * (n - 1))))
    (Measure.pi fun _ : Fin m × Fin n ↦ gaussianReal μ (σ : NNReal)²) :=
    ⟨hφ_meas, hANOVA⟩
  set grid : Ω → Fin m × Fin n → ℝ :=
    fun ω (p : Fin m × Fin n) ↦ y[p.1][p.2] ω
  have hfun :
    (((n : Ω → ℝ) * (∑ i : Fin m, ((∑ j : Fin n, y[i][j]) / (n : Ω → ℝ) - (∑ i : Fin m, ∑ j : Fin n, y[i][j]) / ((m * n : ℕ) : Ω → ℝ)) ^ 2)) / (σ² : Ω → ℝ),
      (∑ i : Fin m, ∑ j : Fin n, (y[i][j] - (∑ k : Fin n, y[i][k]) / (n : Ω → ℝ)) ^ 2) / (σ² : Ω → ℝ)) =
        φ ∘ grid := by
    funext ω
    have hsum :
      ∑ i : Fin m, ∑ j : Fin n, y[i][j] ω =
          ∑ p : Fin m × Fin n, y[p.1][p.2] ω := by
      simpa using
        (Fintype.sum_prod_type
          (f := fun (p : Fin m × Fin n) ↦ y[p.1][p.2] ω)).symm
    simp [JointRandomSymbol, φ, grid, hsum, Function.const, Pi.div_apply, Pi.sub_apply,
      Pi.pow_apply, Pi.mul_apply, Finset.sum_apply, Pi.natCast_apply]
  rw [hfun]
  exact hφ.fun_comp hgrid

-- created on 2026-10-31
