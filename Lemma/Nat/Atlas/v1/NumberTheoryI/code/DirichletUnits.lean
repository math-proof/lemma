import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.DirichletUnits
open NumberField NumberField.Units NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem Module NumberField.mixedEmbedding
open scoped NumberField Classical Polynomial nonZeroDivisors NNReal
open NumberField.Units.dirichletUnitTheorem Module
open NumberField.mixedEmbedding


/--
[logEmbedding_ker_eq_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma logEmbedding_ker_eq_torsion
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  (NumberField.Units.logEmbedding K).ker = (torsion K).toAddSubgroup :=
-- proof
  logEmbedding_ker

/--
[def_15_3_size_hom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma def_15_3_size_hom
  {K : Type*}
  [Field K]
  [NumberField K]
  {I₁ I₂ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K}
  {f₁ f₂ : InfinitePlace K → ℝ} :
-- imply
  def_15_3_size K (I₁ * I₂) (f₁ * f₂) = def_15_3_size K I₁ f₁ * def_15_3_size K I₂ f₂ := by
-- proof
  simp only [def_15_3_size, Pi.mul_apply, mul_pow, Finset.prod_mul_distrib, map_mul, Rat.cast_mul]
  ring

/--
[def_15_3_kernel_contains_princ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma def_15_3_kernel_contains_princ
  {K : Type*}
  [Field K]
  [NumberField K]
  {x : K}
-- given
  (hx : x ≠ 0) :
-- imply
  def_15_3_size K (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x) (fun w => w x) = 1 := by
-- proof
  simp only [def_15_3_size]
  rw [InfinitePlace.prod_eq_abs_norm, FractionalIdeal.absNorm_span_singleton]
  exact div_self (Rat.cast_ne_zero.mpr (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hx)))

/--
[def_15_3_L_subset_I_c](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma def_15_3_L_subset_I_c
  {K : Type*}
  [Field K]
  [NumberField K]
  {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K}
  {f : InfinitePlace K → ℝ} :
-- imply
  def_15_3_L K I f ⊆ (I : Set K) :=
-- proof
  fun _ hx => hx.1

/--
[lem_15_7_unitLattice_spans_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma lem_15_7_unitLattice_spans_top
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  Submodule.span ℝ (unitLattice K : Set (logSpace K)) = ⊤ :=
-- proof
  unitLattice_span_eq_top K

/--
[lem_15_7_unitLattice_discrete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma lem_15_7_unitLattice_discrete
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  DiscreteTopology (unitLattice K) :=
-- proof
  inferInstance

/--
[lem_15_7_unitLattice_inter_ball_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma lem_15_7_unitLattice_inter_ball_finite
  {K : Type*}
  [Field K]
  [NumberField K]
  {r : ℝ} :
-- imply
  ((unitLattice K : Set (logSpace K)) ∩ Metric.closedBall 0 r).Finite :=
-- proof
  unitLattice_inter_ball_finite K r

/--
[def_15_3_L_eq_arakelovL](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma def_15_3_L_eq_arakelovL
  {K : Type*}
  [Field K]
  [NumberField K]
  {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K}
  {f : InfinitePlace K → ℝ} :
-- imply
  def_15_3_L K I f = arakelovL K I f :=
-- proof
  rfl

/--
[lem_15_7_arakelov_L_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma lem_15_7_arakelov_L_finite
  {K : Type*}
  [Field K]
  [NumberField K]
  {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K}
  {f : InfinitePlace K → ℝ} :
-- imply
  Set.Finite (arakelovL K I f) := by
-- proof
  obtain ⟨a, ha_mem, ha_int⟩ := I.isFractional
  have ha_ne : (a : K) ≠ 0 := by
    intro h; apply nonZeroDivisors.ne_zero ha_mem; exact Subtype.val_injective h
  let B := Finset.univ.sup' Finset.univ_nonempty (fun w : InfinitePlace K => w (a : K) * f w)
  apply Set.Finite.of_injOn (f := fun x => (a : K) * x)
    (t := {y : K | IsIntegral ℤ y ∧ ∀ φ : K →+* ℂ, ‖φ y‖ ≤ B})
  · intro x hx
    simp only [Set.mem_setOf_eq, arakelovL] at hx ⊢
    constructor
    · have h := ha_int x hx.1
      obtain ⟨c, hc⟩ := h
      rw [Algebra.smul_def] at hc
      rwa [← hc]
    · intro φ
      rw [map_mul, norm_mul]
      calc ‖φ (a : K)‖ * ‖φ x‖
        = (InfinitePlace.mk φ) (a : K) * ‖φ x‖ := by rw [← InfinitePlace.apply φ]
        _ = (InfinitePlace.mk φ) (a : K) * (InfinitePlace.mk φ) x := by
          rw [← InfinitePlace.apply φ x]
        _ ≤ (InfinitePlace.mk φ) (a : K) * f (InfinitePlace.mk φ) := by
          gcongr; exact hx.2 _
        _ ≤ B := Finset.le_sup'_of_le _ (Finset.mem_univ _) le_rfl
  · intro x _ y _ h
    exact mul_left_cancel₀ ha_ne h
  · exact Embeddings.finite_of_norm_le K ℂ B

/--
[cor_15_8_torsion_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma cor_15_8_torsion_finite
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  Finite (torsion K) :=
-- proof
  inferInstance

/--
[cor_15_8_kernel_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma cor_15_8_kernel_characterization
  {K : Type*}
  [Field K]
  [NumberField K]
  {x : (𝓞 K)ˣ} :
-- imply
  x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1 :=
-- proof
  mem_torsion K

/--
[cor_15_8_logEmbedding_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma cor_15_8_logEmbedding_eq_zero_iff
  {K : Type*}
  [Field K]
  [NumberField K]
  {x : (𝓞 K)ˣ} :
-- imply
  logEmbedding K (Additive.ofMul x) = 0 ↔ x ∈ torsion K :=
-- proof
  logEmbedding_eq_zero_iff

/--
[cor_15_8_torsion_subgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma cor_15_8_torsion_subgroup
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  torsion K = CommGroup.torsion (𝓞 K)ˣ :=
-- proof
  rfl

/--
[cor_15_8_torsion_cyclic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma cor_15_8_torsion_cyclic
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  IsCyclic (torsion K) :=
-- proof
  inferInstance

/--
[prop_15_9_unit_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma prop_15_9_unit_rank
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  finrank ℤ (↥(unitLattice K)) = rank K :=
-- proof
  unitLattice_rank K

/--
[rank_eq_card_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma rank_eq_card_sub_one
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  rank K = Fintype.card (InfinitePlace K) - 1 :=
-- proof
  rfl

/--
[prop_15_9_L_contains_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma prop_15_9_L_contains_nonzero
  {K : Type*}
  [Field K]
  [NumberField K]
  {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
  {f : InfinitePlace K → ℝ≥0}
-- given
  (h : minkowskiBound K I < MeasureTheory.volume (convexBodyLT K f)) :
-- imply
  ∃ a ∈ arakelovL K (I : FractionalIdeal (𝓞 K)⁰ K) (fun w => (f w : ℝ)), a ≠ 0 := by
-- proof
  obtain ⟨a, ha_mem, ha_ne, ha_bd⟩ := exists_ne_zero_mem_ideal_lt K I h
  exact ⟨a, ⟨ha_mem, fun w => le_of_lt (ha_bd w)⟩, ha_ne⟩

/--
[prop_15_11_fundSystem_lattice_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma prop_15_11_fundSystem_lattice_basis
  {K : Type*}
  [Field K]
  [NumberField K]
  {i : Fin (rank K)} :
-- imply
  (logEmbedding K) (Additive.ofMul (fundSystem K i)) = ↑((basisUnitLattice K) i) :=
-- proof
  logEmbedding_fundSystem K i

/--
[prop_15_11_closure_fundSystem_sup_torsion_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma prop_15_11_closure_fundSystem_sup_torsion_eq_top
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  Subgroup.closure (Set.range (fundSystem K)) ⊔ torsion K = ⊤ :=
-- proof
  closure_fundSystem_sup_torsion_eq_top K

/--
[thm_15_12_dirichlet_unit_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma thm_15_12_dirichlet_unit_theorem
  {K : Type*}
  [Field K]
  [NumberField K]
  {x : (𝓞 K)ˣ} :
-- imply
  ∃! ζe : torsion K × (Fin (rank K) → ℤ), x = ζe.1 * ∏ i, (fundSystem K i) ^ (ζe.2 i) :=
-- proof
  exist_unique_eq_mul_prod K x

/--
[thm_15_12_units_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma thm_15_12_units_fg
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  Monoid.FG (𝓞 K)ˣ :=
-- proof
  inferInstance

/--
[thm_15_13_number_field_case](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma thm_15_13_number_field_case
  {K : Type*}
  [Field K]
  [NumberField K]
  {x : (𝓞 K)ˣ} :
-- imply
  ∃! ζe : torsion K × (Fin (rank K) → ℤ), x = ζe.1 * ∏ i, (fundSystem K i) ^ (ζe.2 i) :=
-- proof
  thm_15_12_dirichlet_unit_theorem K x

/--
[def_15_16_regulator_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma def_15_16_regulator_pos
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  0 < regulator K :=
-- proof
  regulator_pos K

/--
[def_15_16_regulator_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma def_15_16_regulator_ne_zero
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  regulator K ≠ 0 :=
-- proof
  regulator_ne_zero K

/--
[def_15_16_regulator_eq_det](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma def_15_16_regulator_eq_det
  {K : Type*}
  [Field K]
  [NumberField K]
  {w' : InfinitePlace K}
-- given
  (e : {w // w ≠ w'} ≃ Fin (rank K)) :
-- imply
  regulator K = :=
-- proof
  regulator_eq_det K w' e

/--
[arakelovDivisor_size_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma arakelovDivisor_size_mul
  {K : Type*}
  [Field K]
  [NumberField K]
  {I₁ I₂ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K}
  {f₁ f₂ : InfinitePlace K → ℝ} :
-- imply
  def_15_3_size K (I₁ * I₂) (f₁ * f₂) = def_15_3_size K I₁ f₁ * def_15_3_size K I₂ f₂ :=
-- proof
  def_15_3_size_hom K I₁ I₂ f₁ f₂

/--
[arakelovDivisor_principal_size_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma arakelovDivisor_principal_size_eq_one
  {K : Type*}
  [Field K]
  [NumberField K]
  {x : K}
-- given
  (hx : x ≠ 0) :
-- imply
  def_15_3_size K (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x) (fun w => w x) = 1 :=
-- proof
  def_15_3_kernel_contains_princ K hx

/--
[arakelovDivisor_L_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma arakelovDivisor_L_subset
  {K : Type*}
  [Field K]
  [NumberField K]
  {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K}
  {f : InfinitePlace K → ℝ} :
-- imply
  def_15_3_L K I f ⊆ (I : Set K) :=
-- proof
  def_15_3_L_subset_I_c K I f

/--
[unitLattice_spans_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma unitLattice_spans_top
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  Submodule.span ℝ (unitLattice K : Set (logSpace K)) = ⊤ :=
-- proof
  lem_15_7_unitLattice_spans_top K

/--
[unitLattice_discreteTopology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma unitLattice_discreteTopology
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  DiscreteTopology (unitLattice K) :=
-- proof
  lem_15_7_unitLattice_discrete K

/--
[arakelovL_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma arakelovL_finite
  {K : Type*}
  [Field K]
  [NumberField K]
  {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K}
  {f : InfinitePlace K → ℝ} :
-- imply
  Set.Finite (arakelovL K I f) :=
-- proof
  lem_15_7_arakelov_L_finite K I f

/--
[torsion_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma torsion_finite
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  Finite (torsion K) :=
-- proof
  cor_15_8_torsion_finite K

/--
[mem_torsion_iff_forall_infinitePlace_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma mem_torsion_iff_forall_infinitePlace_eq_one
  {K : Type*}
  [Field K]
  [NumberField K]
  {x : (𝓞 K)ˣ} :
-- imply
  x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1 :=
-- proof
  cor_15_8_kernel_characterization K

/--
[logEmbedding_eq_zero_iff_mem_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma logEmbedding_eq_zero_iff_mem_torsion
  {K : Type*}
  [Field K]
  [NumberField K]
  {x : (𝓞 K)ˣ} :
-- imply
  logEmbedding K (Additive.ofMul x) = 0 ↔ x ∈ torsion K :=
-- proof
  cor_15_8_logEmbedding_eq_zero_iff K

/--
[torsion_eq_commGroup_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma torsion_eq_commGroup_torsion
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  torsion K = CommGroup.torsion (𝓞 K)ˣ :=
-- proof
  cor_15_8_torsion_subgroup K

/--
[torsion_isCyclic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma torsion_isCyclic
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  IsCyclic (torsion K) :=
-- proof
  cor_15_8_torsion_cyclic K

/--
[rootsOfUnity_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma rootsOfUnity_characterization
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  Finite (torsion K) ∧ IsCyclic (torsion K) ∧ (∀ x : (𝓞 K)ˣ, x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1) :=
-- proof
  ⟨cor_15_8_torsion_finite K, cor_15_8_torsion_cyclic K,
    fun x => cor_15_8_kernel_characterization K⟩

/--
[unitLattice_finrank_eq_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma unitLattice_finrank_eq_rank
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  finrank ℤ (↑(unitLattice K)) = rank K :=
-- proof
  prop_15_9_unit_rank K

/--
[arakelovL_exists_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma arakelovL_exists_ne_zero
  {K : Type*}
  [Field K]
  [NumberField K]
  {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
  {f : InfinitePlace K → ℝ≥0}
-- given
  (h : minkowskiBound K I < MeasureTheory.volume (convexBodyLT K f)) :
-- imply
  ∃ a ∈ arakelovL K (I : FractionalIdeal (𝓞 K)⁰ K) (fun w => (f w : ℝ)), a ≠ 0 :=
-- proof
  prop_15_9_L_contains_nonzero K I h

/--
[logEmbedding_fundSystem_eq_basisUnitLattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma logEmbedding_fundSystem_eq_basisUnitLattice
  {K : Type*}
  [Field K]
  [NumberField K]
  {i : Fin (rank K)} :
-- imply
  (logEmbedding K) (Additive.ofMul (fundSystem K i)) = ↑((basisUnitLattice K) i) :=
-- proof
  prop_15_11_fundSystem_lattice_basis K i

/--
[closure_fundSystem_sup_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma closure_fundSystem_sup_torsion
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  Subgroup.closure (Set.range (fundSystem K)) ⊔ torsion K = ⊤ :=
-- proof
  prop_15_11_closure_fundSystem_sup_torsion_eq_top K

/--
[unit_eq_torsion_mul_fundSystem_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma unit_eq_torsion_mul_fundSystem_pow
  {K : Type*}
  [Field K]
  [NumberField K]
  {x : (𝓞 K)ˣ} :
-- imply
  ∃! ζe : torsion K × (Fin (rank K) → ℤ), x = ζe.1 * ∏ i, (fundSystem K i) ^ (ζe.2 i) :=
-- proof
  thm_15_12_dirichlet_unit_theorem K x

/--
[units_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma units_fg
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  Monoid.FG (𝓞 K)ˣ :=
-- proof
  thm_15_12_units_fg K

/--
[numberField_unit_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma numberField_unit_decomposition
  {K : Type*}
  [Field K]
  [NumberField K]
  {x : (𝓞 K)ˣ} :
-- imply
  ∃! ζe : torsion K × (Fin (rank K) → ℤ), x = ζe.1 * ∏ i, (fundSystem K i) ^ (ζe.2 i) :=
-- proof
  thm_15_13_number_field_case K x

/--
[regulator_pos_of_numberField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma regulator_pos_of_numberField
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  0 < regulator K :=
-- proof
  def_15_16_regulator_pos K

/--
[regulator_ne_zero_of_numberField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma regulator_ne_zero_of_numberField
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  regulator K ≠ 0 :=
-- proof
  def_15_16_regulator_ne_zero K

/--
[regulator_eq_det_of_fundSystem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean)
-/
@[path]
lemma regulator_eq_det_of_fundSystem
  {K : Type*}
  [Field K]
  [NumberField K]
  {w' : InfinitePlace K}
-- given
  (e : {w // w ≠ w'} ≃ Fin (rank K)) :
-- imply
  regulator K = :=
-- proof
  def_15_16_regulator_eq_det K w' e


-- created on 2026-10-23
