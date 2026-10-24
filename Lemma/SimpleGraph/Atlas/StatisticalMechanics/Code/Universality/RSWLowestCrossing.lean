import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWLowestCrossing
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_cornerReturn_support_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_cornerReturn_support_inside_eq
  {n : ℤ}
  {x : topSide 0 (2 * n) (-n) n}
  {z : rightSide 0 (2 * n) (-n) n}
  {p : Site 2}
-- given
  (hp : p ∈ (rlc_cornerReturn x z).support)
  (hpR : p ∈ rect 0 (2 * n) (-n) n) :
-- imply
  p = (z : Site 2) ∨ p = (x : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_cornerReturn_support_inside x z hp hpR

/--
[rlc_cornerReturn_rayCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_cornerReturn_rayCount_zero_eq
  {n : ℤ}
  {x : topSide 0 (2 * n) (-n) n}
  {z : rightSide 0 (2 * n) (-n) n}
  {p : Site 2}
-- given
  (hpR : p ∈ rect 0 (2 * n) (-n) n) :
-- imply
  jec_rayCount p (rlc_cornerReturn x z) = 0 := by
-- proof
  apply StatMech.Universality.rlc_cornerReturn_rayCount_zero x z p hpR

/--
[rlc_ray_eq_below_right_of_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_ray_eq_below_right_of_avoids_eq
  {n : ℤ}
  {t : rightSide 0 (2 * n) (-n) n}
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
-- given
  (hbox : ∀ p ∈ w.support, p ∈ rect 0 (2 * n) (-n) n)
  (havoid : (t : Site 2) ∉ w.support) :
-- imply
  jec_rayCount (t : Site 2) w = crossCount (jec_belowSet ((t : Site 2) 1)) w := by
-- proof
  apply StatMech.Universality.rlc_ray_eq_below_right_of_avoids t w hbox havoid

/--
[rlc_harris_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_harris_cylinder_eq
  [Countable E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {T U : Finset E}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hAinc : IsIncreasing A)
  (hBinc : IsIncreasing B)
  (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (T : Set E))
  (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set E)) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B ≤ (bernoulliProductMeasure (E := E) p hp).real (A ∩ B) := by
-- proof
  apply StatMech.Universality.rlc_harris_cylinder p hp hAinc hBinc T U hA hB

/--
[rlc_harris_three_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_harris_three_cylinder_eq
  [Countable E]
  [DecidableEq E]
  {A B C : Set (ConfigSpace E)}
  {T U V : Finset E}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hAinc : IsIncreasing A)
  (hBinc : IsIncreasing B)
  (hCinc : IsIncreasing C)
  (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (T : Set E))
  (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set E))
  (hC : DependsOn (C.indicator (fun _ => (1 : ℝ))) (V : Set E)) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B * (bernoulliProductMeasure (E := E) p hp).real C ≤ (bernoulliProductMeasure (E := E) p hp).real (A ∩ B ∩ C) := by
-- proof
  apply StatMech.Universality.rlc_harris_three_cylinder p hp hAinc hBinc hCinc T U V hA hB hC

/--
[rlc_diagonal_event_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_diagonal_event_lower_bound_eq
  [Countable E]
  [DecidableEq E]
  {α : ℝ}
  {A B C Diag : Set (ConfigSpace E)}
  {T U V : Finset E}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hα : 0 ≤ α)
  (hAinc : IsIncreasing A)
  (hBinc : IsIncreasing B)
  (hCinc : IsIncreasing C)
  (hAdep : DependsOn (A.indicator (fun _ => (1 : ℝ))) (T : Set E))
  (hBdep : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set E))
  (hCdep : DependsOn (C.indicator (fun _ => (1 : ℝ))) (V : Set E))
  (hAprob : α / 2 ≤ (bernoulliProductMeasure (E := E) p hp).real A)
  (hBprob : α / 2 ≤ (bernoulliProductMeasure (E := E) p hp).real B)
  (hCprob : α ≤ (bernoulliProductMeasure (E := E) p hp).real C)
  (hforce : A ∩ B ∩ C ⊆ Diag) :
-- imply
  α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real Diag := by
-- proof
  apply StatMech.Universality.rlc_diagonal_event_lower_bound p hp α hα A B C Diag T U V hAinc hBinc hCinc hAdep hBdep hCdep hAprob hBprob hCprob hforce

/--
[rlc_connector_half_of_dual_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connector_half_of_dual_reflection_eq
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {sigma : ConfigSpace E → ConfigSpace E}
  {Connect : Set (ConfigSpace E)}
-- given
  (hsigma : MeasurePreserving sigma mu mu)
  (hConnect : MeasurableSet Connect)
  (hdual : Connectᶜ ⊆ sigma ⁻¹' Connect) :
-- imply
  (1 : ℝ) / 2 ≤ mu.real Connect := by
-- proof
  apply StatMech.Universality.rlc_connector_half_of_dual_reflection mu sigma hsigma Connect hConnect hdual

/--
[rlc_connector_half_of_dual_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connector_half_of_dual_comparison_eq
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {sigma : ConfigSpace E → ConfigSpace E}
  {Connect DualConnect : Set (ConfigSpace E)}
-- given
  (hsigma : MeasurePreserving sigma mu mu)
  (hConnect : MeasurableSet Connect)
  (hDualConnect : MeasurableSet DualConnect)
  (hdual : Connectᶜ ⊆ sigma ⁻¹' DualConnect)
  (hcompare : mu.real DualConnect ≤ mu.real Connect) :
-- imply
  (1 : ℝ) / 2 ≤ mu.real Connect := by
-- proof
  apply StatMech.Universality.rlc_connector_half_of_dual_comparison mu sigma hsigma Connect DualConnect hConnect hDualConnect hdual hcompare

/--
[rlc_mem_firstWitness_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_firstWitness_iff_eq
  {N : ℕ}
  {W : Fin N → Set (ConfigSpace E)}
  {i : Fin N}
  {omega : ConfigSpace E} :
-- imply
  omega ∈ rlc_firstWitness W i ↔ omega ∈ W i ∧ ∀ j : Fin N, j < i → omega ∉ W j := by
-- proof
  apply StatMech.Universality.rlc_mem_firstWitness_iff

/--
[rlc_firstWitness_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_firstWitness_pairwiseDisjoint_eq
  {N : ℕ}
  {W : Fin N → Set (ConfigSpace E)} :
-- imply
  Pairwise (Disjoint on rlc_firstWitness W) := by
-- proof
  apply StatMech.Universality.rlc_firstWitness_pairwiseDisjoint W

/--
[rlc_iUnion_firstWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_iUnion_firstWitness_eq
  {N : ℕ}
  {W : Fin N → Set (ConfigSpace E)} :
-- imply
  (⋃ i, rlc_firstWitness W i) = ⋃ i, W i := by
-- proof
  apply StatMech.Universality.rlc_iUnion_firstWitness W

/--
[rlc_mem_exploredSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_exploredSupport_eq
  {N : ℕ}
  [DecidableEq E]
  {T : Fin N → Finset E}
  {i j : Fin N}
  {e : E}
-- given
  (hji : j ≤ i)
  (he : e ∈ T j) :
-- imply
  e ∈ rlc_exploredSupport T i := by
-- proof
  apply StatMech.Universality.rlc_mem_exploredSupport hji he

/--
[rlc_firstWitness_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_firstWitness_dependsOn_eq
  {N : ℕ}
  [DecidableEq E]
  {W : Fin N → Set (ConfigSpace E)}
  {T : Fin N → Finset E}
  {i : Fin N}
-- given
  (hW : ∀ i, DependsOn ((W i).indicator (fun _ => (1 : ℝ))) (T i : Set E)) :
-- imply
  DependsOn ((rlc_firstWitness W i).indicator (fun _ => (1 : ℝ))) (rlc_exploredSupport T i : Set E) := by
-- proof
  apply StatMech.Universality.rlc_firstWitness_dependsOn W T hW i

/--
[rlc_firstWitness_inter_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_firstWitness_inter_pairwiseDisjoint_eq
  {N : ℕ}
  {W X : Fin N → Set (ConfigSpace E)} :
-- imply
  Pairwise (Disjoint on fun i => rlc_firstWitness W i ∩ X i) := by
-- proof
  apply StatMech.Universality.rlc_firstWitness_inter_pairwiseDisjoint W X

/--
[rlc_exploration_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_exploration_lower_bound_eq
  {N : ℕ}
  [Countable E]
  [DecidableEq E]
  {W X : Fin N → Set (ConfigSpace E)}
  {T U : Fin N → Finset E}
  {Goal : Set (ConfigSpace E)}
  {c : ℝ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (_hc : 0 ≤ c)
  (hW : ∀ i, DependsOn ((W i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
  (hX : ∀ i, DependsOn ((X i).indicator (fun _ => (1 : ℝ))) (U i : Set E))
  (hdisj : ∀ i, Disjoint (rlc_exploredSupport T i) (U i))
  (hprob : ∀ i, c ≤ (bernoulliProductMeasure (E := E) p hp).real (X i))
  (hglue : ∀ i, rlc_firstWitness W i ∩ X i ⊆ Goal) :
-- imply
  c * (bernoulliProductMeasure (E := E) p hp).real (⋃ i, W i) ≤ (bernoulliProductMeasure (E := E) p hp).real Goal := by
-- proof
  apply StatMech.Universality.rlc_exploration_lower_bound p hp W X T U Goal c _hc hW hX hdisj hprob hglue

/--
[rlc_stoppingPartition_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_stoppingPartition_lower_bound_eq
  [Fintype I]
  [Countable E]
  [DecidableEq E]
  {H Goal : Set (ConfigSpace E)}
  {Part X : I → Set (ConfigSpace E)}
  {T U : I → Finset E}
  {c : ℝ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (_hc : 0 ≤ c)
  (hpart : (⋃ i, Part i) = H)
  (hpair : Pairwise (Disjoint on Part))
  (hPart : ∀ i, DependsOn ((Part i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
  (hX : ∀ i, DependsOn ((X i).indicator (fun _ => (1 : ℝ))) (U i : Set E))
  (hdisj : ∀ i, Disjoint (T i) (U i))
  (hprob : ∀ i, c ≤ (bernoulliProductMeasure (E := E) p hp).real (X i))
  (hglue : ∀ i, Part i ∩ X i ⊆ Goal) :
-- imply
  c * (bernoulliProductMeasure (E := E) p hp).real H ≤ (bernoulliProductMeasure (E := E) p hp).real Goal := by
-- proof
  apply StatMech.Universality.rlc_stoppingPartition_lower_bound p hp H Goal Part X T U c _hc hpart hpair hPart hX hdisj hprob hglue

/--
[rlc_bernoulli_rsw_stopping_sixth_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_bernoulli_rsw_stopping_sixth_power_eq
  [Fintype I]
  [Countable E]
  [DecidableEq E]
  {α : ℝ}
  {E₀ E₁ Goal : Set (ConfigSpace E)}
  {S₀ S₁ : Finset E}
  {Part X : I → Set (ConfigSpace E)}
  {T U : I → Finset E}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hα : 0 ≤ α)
  (hE₀inc : IsIncreasing E₀)
  (hE₁inc : IsIncreasing E₁)
  (hE₀dep : DependsOn (E₀.indicator (fun _ => (1 : ℝ))) (S₀ : Set E))
  (hE₁dep : DependsOn (E₁.indicator (fun _ => (1 : ℝ))) (S₁ : Set E))
  (hE₀prob : α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real E₀)
  (hE₁prob : α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real E₁)
  (hpart : (⋃ i, Part i) = E₀ ∩ E₁)
  (hpair : Pairwise (Disjoint on Part))
  (hPart : ∀ i, DependsOn ((Part i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
  (hX : ∀ i, DependsOn ((X i).indicator (fun _ => (1 : ℝ))) (U i : Set E))
  (hdisj : ∀ i, Disjoint (T i) (U i))
  (hconnector : ∀ i, (1 : ℝ) / 2 ≤ (bernoulliProductMeasure (E := E) p hp).real (X i))
  (hglue : ∀ i, Part i ∩ X i ⊆ Goal) :
-- imply
  α ^ 6 / 32 ≤ (bernoulliProductMeasure (E := E) p hp).real Goal := by
-- proof
  apply StatMech.Universality.rlc_bernoulli_rsw_stopping_sixth_power p hp α hα E₀ E₁ Goal S₀ S₁ hE₀inc hE₁inc hE₀dep hE₁dep hE₀prob hE₁prob Part X T U hpart hpair hPart hX hdisj hconnector hglue

/--
[rlc_bernoulli_rsw_sixth_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_bernoulli_rsw_sixth_power_eq
  {N : ℕ}
  [Countable E]
  [DecidableEq E]
  {α : ℝ}
  {E₀ E₁ Goal : Set (ConfigSpace E)}
  {S₀ S₁ : Finset E}
  {W X : Fin N → Set (ConfigSpace E)}
  {T U : Fin N → Finset E}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hα : 0 ≤ α)
  (hE₀inc : IsIncreasing E₀)
  (hE₁inc : IsIncreasing E₁)
  (hE₀dep : DependsOn (E₀.indicator (fun _ => (1 : ℝ))) (S₀ : Set E))
  (hE₁dep : DependsOn (E₁.indicator (fun _ => (1 : ℝ))) (S₁ : Set E))
  (hE₀prob : α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real E₀)
  (hE₁prob : α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real E₁)
  (hpartition : (⋃ i, W i) = E₀ ∩ E₁)
  (hW : ∀ i, DependsOn ((W i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
  (hX : ∀ i, DependsOn ((X i).indicator (fun _ => (1 : ℝ))) (U i : Set E))
  (hdisj : ∀ i, Disjoint (rlc_exploredSupport T i) (U i))
  (hconnector : ∀ i, (1 : ℝ) / 2 ≤ (bernoulliProductMeasure (E := E) p hp).real (X i))
  (hglue : ∀ i, rlc_firstWitness W i ∩ X i ⊆ Goal) :
-- imply
  α ^ 6 / 32 ≤ (bernoulliProductMeasure (E := E) p hp).real Goal := by
-- proof
  apply StatMech.Universality.rlc_bernoulli_rsw_sixth_power p hp α hα E₀ E₁ Goal S₀ S₁ hE₀inc hE₁inc hE₀dep hE₁dep hE₀prob hE₁prob W X T U hpartition hW hX hdisj hconnector hglue

/--
[rlc_mem_rectFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_rectFinset_eq
  {a b c d : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rlc_rectFinset a b c d ↔ x ∈ rect a b c d := by
-- proof
  apply StatMech.Universality.rlc_mem_rectFinset

/--
[rlc_mem_verticalSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_verticalSegment_eq
  {a b c d x₀ lo hi : ℤ}
  {z : rect a b c d} :
-- imply
  z ∈ rlc_verticalSegment a b c d x₀ lo hi ↔ (z : Site 2) 0 = x₀ ∧ lo ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ hi := by
-- proof
  apply StatMech.Universality.rlc_mem_verticalSegment

/--
[rlc_betweenEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_betweenEvent_isIncreasing_eq
  {a b c d : ℤ}
  {P Q : Finset (rect a b c d)} :
-- imply
  IsIncreasing (rlc_betweenEvent P Q) := by
-- proof
  apply StatMech.Universality.rlc_betweenEvent_isIncreasing P Q

/--
[rlc_betweenEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_betweenEvent_dependsOn_eq
  {a b c d : ℤ}
  {P Q : Finset (rect a b c d)} :
-- imply
  DependsOn ((rlc_betweenEvent P Q).indicator (fun _ => (1 : ℝ))) (StatMech.Percolation.edgesWithinFinset (rlc_rectFinset a b c d) : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_betweenEvent_dependsOn P Q

/--
[rlc_betweenEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_betweenEvent_measurableSet_eq
  {a b c d : ℤ}
  {P Q : Finset (rect a b c d)} :
-- imply
  MeasurableSet (rlc_betweenEvent P Q) := by
-- proof
  apply StatMech.Universality.rlc_betweenEvent_measurableSet P Q

/--
[rlc_betweenPathOpen_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_betweenPathOpen_dependsOn_eq
  {a b c d : ℤ}
  {P Q : Finset (rect a b c d)}
  {gamma : RlcBetweenPath P Q} :
-- imply
  DependsOn ((rlc_betweenPathOpen gamma).indicator (fun _ => (1 : ℝ))) (rlc_betweenPathEdges gamma : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_betweenPathOpen_dependsOn gamma

/--
[rlc_pathOpen_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathOpen_dependsOn_eq
  {a b c d : ℤ}
  {gamma : RlcCrossingPath a b c d} :
-- imply
  DependsOn ((rlc_pathOpen gamma).indicator (fun _ => (1 : ℝ))) (rlc_pathEdges gamma : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_pathOpen_dependsOn gamma

/--
[rlc_pathOpen_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathOpen_measurableSet_eq
  {a b c d : ℤ}
  {gamma : RlcCrossingPath a b c d} :
-- imply
  MeasurableSet (rlc_pathOpen gamma) := by
-- proof
  apply StatMech.Universality.rlc_pathOpen_measurableSet gamma

/--
[rlc_edges_mapLe_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_edges_mapLe_eq_eq
  {G G' : SimpleGraph V}
  {u v : V}
  {w : G.Walk u v}
-- given
  (h : G ≤ G') :
-- imply
  (w.mapLe h).edges = w.edges := by
-- proof
  apply StatMech.Universality.rlc_edges_mapLe_eq h w

/--
[rlc_iUnion_pathOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_iUnion_pathOpen_eq
  {a b c d : ℤ} :
-- imply
  (⋃ gamma : RlcCrossingPath a b c d, rlc_pathOpen gamma) = horizontalCrossingEvent a b c d := by
-- proof
  apply StatMech.Universality.rlc_iUnion_pathOpen a b c d

/--
[rlc_iUnion_betweenPathOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_iUnion_betweenPathOpen_eq
  {a b c d : ℤ}
  {P Q : Finset (rect a b c d)} :
-- imply
  (⋃ gamma : RlcBetweenPath P Q, rlc_betweenPathOpen gamma) = rlc_betweenEvent P Q := by
-- proof
  apply StatMech.Universality.rlc_iUnion_betweenPathOpen P Q

/--
[rlc_horizontalCrossingEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_horizontalCrossingEvent_measurableSet_eq
  {a b c d : ℤ} :
-- imply
  MeasurableSet (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rlc_horizontalCrossingEvent_measurableSet a b c d

/--
[rlc_verticalCrossingEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_verticalCrossingEvent_dependsOn_eq
  {a b c d : ℤ} :
-- imply
  DependsOn ((verticalCrossingEvent a b c d).indicator (fun _ => (1 : ℝ))) (edgesWithinFinset (rect_finite a b c d).toFinset : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_verticalCrossingEvent_dependsOn a b c d

/--
[rlc_verticalCrossingEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_verticalCrossingEvent_measurableSet_eq
  {a b c d : ℤ} :
-- imply
  MeasurableSet (verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rlc_verticalCrossingEvent_measurableSet a b c d

/--
[rlc_lrRestrictedEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_lrRestrictedEvent_isIncreasing_eq
  {a b c d : ℤ}
  {L R : Set (Site 2)} :
-- imply
  IsIncreasing (rlc_lrRestrictedEvent a b c d L R) := by
-- proof
  apply StatMech.Universality.rlc_lrRestrictedEvent_isIncreasing a b c d L R

/--
[rlc_lrRestrictedEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_lrRestrictedEvent_dependsOn_eq
  {a b c d : ℤ}
  {L R : Set (Site 2)} :
-- imply
  DependsOn ((rlc_lrRestrictedEvent a b c d L R).indicator (fun _ => (1 : ℝ))) (edgesWithinFinset (rect_finite a b c d).toFinset : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_lrRestrictedEvent_dependsOn a b c d L R

/--
[rlc_rightDiagonal_of_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightDiagonal_of_three_eq
  {n : ℤ}
-- given
  (hn : 0 < n) :
-- imply
  rlc_rightToUpper n ∩ rlc_lowerToRight n ∩ verticalCrossingEvent 0 (2 * n) (-n) n ⊆ rlc_rightDiagonal n := by
-- proof
  apply StatMech.Universality.rlc_rightDiagonal_of_three n hn

/--
[rlc_flipY_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipY_zero_eq
  {x : Site 2} :
-- imply
  rlc_flipY x 0 = x 0 := by
-- proof
  apply StatMech.Universality.rlc_flipY_zero x

/--
[rlc_flipY_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipY_one_eq
  {x : Site 2} :
-- imply
  rlc_flipY x 1 = -x 1 := by
-- proof
  apply StatMech.Universality.rlc_flipY_one x

/--
[rlc_flipY_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipY_involutive_eq
  {x : Site 2} :
-- imply
  rlc_flipY (rlc_flipY x) = x := by
-- proof
  apply StatMech.Universality.rlc_flipY_involutive x

/--
[rlc_adj_flipY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_adj_flipY_eq
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj x y ↔ (hypercubicLattice 2).Adj (rlc_flipY x) (rlc_flipY y) := by
-- proof
  apply StatMech.Universality.rlc_adj_flipY x y

/--
[rlc_flipYEdge_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipYEdge_symm_apply_eq
  {e : Sym2 (Site 2)} :
-- imply
  rlc_flipYEdge.symm e = e.map rlc_flipY := by
-- proof
  apply StatMech.Universality.rlc_flipYEdge_symm_apply e

/--
[rlc_flipYConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipYConfig_apply_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  rlc_flipYConfig omega e = omega (e.map rlc_flipY) := by
-- proof
  apply StatMech.Universality.rlc_flipYConfig_apply omega e

/--
[rlc_measurable_flipYConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_measurable_flipYConfig_eq :
-- imply
  Measurable rlc_flipYConfig := by
-- proof
  apply StatMech.Universality.rlc_measurable_flipYConfig

/--
[rlc_flipY_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipY_measurePreserving_eq
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  MeasurePreserving rlc_flipYConfig (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) := by
-- proof
  apply StatMech.Universality.rlc_flipY_measurePreserving p hp

/--
[rlc_mem_centeredRect_flipY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_centeredRect_flipY_eq
  {a b n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rect a b (-n) n ↔ rlc_flipY x ∈ rect a b (-n) n := by
-- proof
  apply StatMech.Universality.rlc_mem_centeredRect_flipY a b n x

/--
[rlc_mem_leftSide_flipY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_leftSide_flipY_eq
  {a b n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ leftSide a b (-n) n ↔ rlc_flipY x ∈ leftSide a b (-n) n := by
-- proof
  apply StatMech.Universality.rlc_mem_leftSide_flipY a b n x

/--
[rlc_mem_rightSide_flipY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_rightSide_flipY_eq
  {a b n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rightSide a b (-n) n ↔ rlc_flipY x ∈ rightSide a b (-n) n := by
-- proof
  apply StatMech.Universality.rlc_mem_rightSide_flipY a b n x

/--
[rlc_isOpenEdge_flipY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_isOpenEdge_flipY_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2} :
-- imply
  IsOpenEdge 2 (rlc_flipYConfig omega) x y ↔ IsOpenEdge 2 omega (rlc_flipY x) (rlc_flipY y) := by
-- proof
  apply StatMech.Universality.rlc_isOpenEdge_flipY omega x y

/--
[rlc_flipY_lrRestricted_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipY_lrRestricted_iff_eq
  {a b n : ℤ}
  {L R : Set (Site 2)}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  omega ∈ rlc_lrRestrictedEvent a b (-n) n L R → rlc_flipYConfig omega ∈ rlc_lrRestrictedEvent a b (-n) n (rlc_flipY '' L) (rlc_flipY '' R) := by
-- proof
  apply StatMech.Universality.rlc_flipY_lrRestricted_iff a b n L R omega

/--
[rlc_flipY_image_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipY_image_univ_eq :
-- imply
  rlc_flipY '' (Set.univ : Set (Site 2)) = Set.univ := by
-- proof
  apply StatMech.Universality.rlc_flipY_image_univ

/--
[rlc_flipY_image_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipY_image_upper_eq :
-- imply
  rlc_flipY '' rlc_upperHalf = rlc_lowerHalf := by
-- proof
  apply StatMech.Universality.rlc_flipY_image_upper

/--
[rlc_flipY_image_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipY_image_lower_eq :
-- imply
  rlc_flipY '' rlc_lowerHalf = rlc_upperHalf := by
-- proof
  apply StatMech.Universality.rlc_flipY_image_lower

/--
[rlc_flipYConfig_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipYConfig_involutive_eq
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  rlc_flipYConfig (rlc_flipYConfig omega) = omega := by
-- proof
  apply StatMech.Universality.rlc_flipYConfig_involutive omega

/--
[rlc_flip_rightToUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flip_rightToUpper_eq
  {n : ℤ}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : omega ∈ rlc_rightToUpper n) :
-- imply
  rlc_flipYConfig omega ∈ rlc_rightToLower n := by
-- proof
  apply StatMech.Universality.rlc_flip_rightToUpper n h

/--
[rlc_flip_rightToLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flip_rightToLower_eq
  {n : ℤ}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : omega ∈ rlc_rightToLower n) :
-- imply
  rlc_flipYConfig omega ∈ rlc_rightToUpper n := by
-- proof
  apply StatMech.Universality.rlc_flip_rightToLower n h

/--
[rlc_flip_lowerToRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flip_lowerToRight_eq
  {n : ℤ}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : omega ∈ rlc_lowerToRight n) :
-- imply
  rlc_flipYConfig omega ∈ rlc_upperToRight n := by
-- proof
  apply StatMech.Universality.rlc_flip_lowerToRight n h

/--
[rlc_flip_upperToRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flip_upperToRight_eq
  {n : ℤ}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : omega ∈ rlc_upperToRight n) :
-- imply
  rlc_flipYConfig omega ∈ rlc_lowerToRight n := by
-- proof
  apply StatMech.Universality.rlc_flip_upperToRight n h

/--
[rlc_rightToUpper_reflection_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightToUpper_reflection_prob_eq
  {n : ℤ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_rightToUpper n) = (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_rightToLower n) := by
-- proof
  apply StatMech.Universality.rlc_rightToUpper_reflection_prob p hp n

/--
[rlc_lowerToRight_reflection_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_lowerToRight_reflection_prob_eq
  {n : ℤ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_lowerToRight n) = (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_upperToRight n) := by
-- proof
  apply StatMech.Universality.rlc_lowerToRight_reflection_prob p hp n

/--
[rlc_horizontal_subset_right_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_horizontal_subset_right_halves_eq
  {n : ℤ} :
-- imply
  horizontalCrossingEvent 0 (2 * n) (-n) n ⊆ rlc_rightToUpper n ∪ rlc_rightToLower n := by
-- proof
  apply StatMech.Universality.rlc_horizontal_subset_right_halves n

/--
[rlc_horizontal_subset_left_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_horizontal_subset_left_halves_eq
  {n : ℤ} :
-- imply
  horizontalCrossingEvent 0 (2 * n) (-n) n ⊆ rlc_lowerToRight n ∪ rlc_upperToRight n := by
-- proof
  apply StatMech.Universality.rlc_horizontal_subset_left_halves n

/--
[rlc_rightToUpper_half_localization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightToUpper_half_localization_eq
  {n : ℤ}
  {alpha : ℝ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hcross : alpha ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (horizontalCrossingEvent 0 (2 * n) (-n) n)) :
-- imply
  alpha / 2 ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_rightToUpper n) := by
-- proof
  apply StatMech.Universality.rlc_rightToUpper_half_localization p hp n alpha hcross

/--
[rlc_lowerToRight_half_localization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_lowerToRight_half_localization_eq
  {n : ℤ}
  {alpha : ℝ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hcross : alpha ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (horizontalCrossingEvent 0 (2 * n) (-n) n)) :
-- imply
  alpha / 2 ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_lowerToRight n) := by
-- proof
  apply StatMech.Universality.rlc_lowerToRight_half_localization p hp n alpha hcross

/--
[rlc_verticalCrossing_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_verticalCrossing_dependsOn_eq
  {a b c d : ℤ} :
-- imply
  DependsOn ((verticalCrossingEvent a b c d).indicator (fun _ => (1 : ℝ))) (edgesWithinFinset (rect_finite a b c d).toFinset : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_verticalCrossing_dependsOn a b c d

/--
[rlc_rightDiagonal_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightDiagonal_lower_bound_eq
  {n : ℤ}
  {alpha : ℝ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hn : 0 < n)
  (halpha : 0 ≤ alpha)
  (hH : alpha ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (horizontalCrossingEvent 0 (2 * n) (-n) n))
  (hV : alpha ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (verticalCrossingEvent 0 (2 * n) (-n) n)) :
-- imply
  alpha ^ 3 / 4 ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_rightDiagonal n) := by
-- proof
  apply StatMech.Universality.rlc_rightDiagonal_lower_bound p hp n hn alpha halpha hH hV

/--
[rlc_leftShift_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftShift_zero_eq
  {n : ℤ} :
-- imply
  rlc_leftShift n 0 = -2 * n := by
-- proof
  apply StatMech.Universality.rlc_leftShift_zero n

/--
[rlc_leftShift_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftShift_one_eq
  {n : ℤ} :
-- imply
  rlc_leftShift n 1 = 0 := by
-- proof
  apply StatMech.Universality.rlc_leftShift_one n

/--
[rlc_leftShift_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftShift_rect_eq
  {n : ℤ} :
-- imply
  rect (0 + rlc_leftShift n 0) (2 * n + rlc_leftShift n 0) (-n + rlc_leftShift n 1) (n + rlc_leftShift n 1) = rect (-2 * n) 0 (-n) n := by
-- proof
  apply StatMech.Universality.rlc_leftShift_rect n

/--
[rlc_translate_rightDiagonal_to_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_translate_rightDiagonal_to_left_eq
  {n : ℤ}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : translateConfig (rlc_leftShift n) omega ∈ rlc_rightDiagonal n) :
-- imply
  omega ∈ rlc_leftDiagonal n := by
-- proof
  apply StatMech.Universality.rlc_translate_rightDiagonal_to_left n omega h

/--
[rlc_translate_leftDiagonal_to_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_translate_leftDiagonal_to_right_eq
  {n : ℤ}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : omega ∈ rlc_leftDiagonal n) :
-- imply
  translateConfig (rlc_leftShift n) omega ∈ rlc_rightDiagonal n := by
-- proof
  apply StatMech.Universality.rlc_translate_leftDiagonal_to_right n omega h

/--
[rlc_leftDiagonal_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftDiagonal_preimage_eq
  {n : ℤ} :
-- imply
  translateConfig (rlc_leftShift n) ⁻¹' rlc_rightDiagonal n = rlc_leftDiagonal n := by
-- proof
  apply StatMech.Universality.rlc_leftDiagonal_preimage n

/--
[rlc_leftDiagonal_prob_eq_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftDiagonal_prob_eq_right_eq
  {n : ℤ} :
-- imply
  rba_selfDualMeasure.real (rlc_leftDiagonal n) = rba_selfDualMeasure.real (rlc_rightDiagonal n) := by
-- proof
  apply StatMech.Universality.rlc_leftDiagonal_prob_eq_right n

/--
[rlc_iUnion_restrictedPathOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_iUnion_restrictedPathOpen_eq
  {a b c d : ℤ}
  {L R : Set (Site 2)} :
-- imply
  (⋃ gamma : RlcRestrictedCrossingPath a b c d L R, rlc_pathOpen gamma.1) = rlc_lrRestrictedEvent a b c d L R := by
-- proof
  apply StatMech.Universality.rlc_iUnion_restrictedPathOpen a b c d L R

/--
[rlc_rot180_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rot180_zero_eq
  {x : Site 2} :
-- imply
  rlc_rot180 x 0 = -x 0 := by
-- proof
  apply StatMech.Universality.rlc_rot180_zero x

/--
[rlc_rot180_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rot180_one_eq
  {x : Site 2} :
-- imply
  rlc_rot180 x 1 = -x 1 := by
-- proof
  apply StatMech.Universality.rlc_rot180_one x

/--
[rlc_rot180_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rot180_involutive_eq
  {x : Site 2} :
-- imply
  rlc_rot180 (rlc_rot180 x) = x := by
-- proof
  apply StatMech.Universality.rlc_rot180_involutive x

/--
[rlc_rot180Edge_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rot180Edge_involutive_eq
  {e : Sym2 (Site 2)} :
-- imply
  Sym2.map rlc_rot180 (Sym2.map rlc_rot180 e) = e := by
-- proof
  apply StatMech.Universality.rlc_rot180Edge_involutive e

/--
[rlc_adj_rot180](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_adj_rot180_eq
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj x y ↔ (hypercubicLattice 2).Adj (rlc_rot180 x) (rlc_rot180 y) := by
-- proof
  apply StatMech.Universality.rlc_adj_rot180 x y

/--
[rlc_rot180_mem_rightRect_iff_leftRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rot180_mem_rightRect_iff_leftRect_eq
  {n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rect 0 (2 * n) (-n) n ↔ rlc_rot180 x ∈ rect (-2 * n) 0 (-n) n := by
-- proof
  apply StatMech.Universality.rlc_rot180_mem_rightRect_iff_leftRect n x

/--
[rlc_rot180RightInducedHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rot180RightInducedHom_injective_eq
  {n : ℤ} :
-- imply
  Function.Injective (rlc_rot180RightInducedHom n) := by
-- proof
  apply StatMech.Universality.rlc_rot180RightInducedHom_injective n

/--
[rlc_rot180_mem_leftRect_iff_rightRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rot180_mem_leftRect_iff_rightRect_eq
  {n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rect (-2 * n) 0 (-n) n ↔ rlc_rot180 x ∈ rect 0 (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_rot180_mem_leftRect_iff_rightRect n x

/--
[rlc_rot180LeftInducedHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rot180LeftInducedHom_injective_eq
  {n : ℤ} :
-- imply
  Function.Injective (rlc_rot180LeftInducedHom n) := by
-- proof
  apply StatMech.Universality.rlc_rot180LeftInducedHom_injective n

/--
[rlc_iUnion_rightDiagonalPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_iUnion_rightDiagonalPath_eq
  {n : ℤ} :
-- imply
  (⋃ gamma : RlcRightDiagonalPath n, rlc_pathOpen gamma.1) = rlc_rightDiagonal n := by
-- proof
  apply StatMech.Universality.rlc_iUnion_rightDiagonalPath n

/--
[rlc_iUnion_leftDiagonalPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_iUnion_leftDiagonalPath_eq
  {n : ℤ} :
-- imply
  (⋃ gamma : RlcLeftDiagonalPath n, rlc_pathOpen gamma.1) = rlc_leftDiagonal n := by
-- proof
  apply StatMech.Universality.rlc_iUnion_leftDiagonalPath n

/--
[rlc_pathPairOpen_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathPairOpen_dependsOn_eq
  {n : ℤ}
  {pair : RlcDiagonalPathPair n} :
-- imply
  DependsOn ((rlc_pathPairOpen pair).indicator (fun _ => (1 : ℝ))) (rlc_pathPairEdges pair : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_pathPairOpen_dependsOn pair

/--
[rlc_iUnion_pathPairOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_iUnion_pathPairOpen_eq
  {n : ℤ} :
-- imply
  (⋃ pair : RlcDiagonalPathPair n, rlc_pathPairOpen pair) = rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
-- proof
  apply StatMech.Universality.rlc_iUnion_pathPairOpen n

/--
[rlc_rightPath_arcSeparatingSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPath_arcSeparatingSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  ArcSeparatingSet (rlc_swappedRightPathSupport gamma) (-n) n 0 (2 * n) := by
-- proof
  apply StatMech.Universality.rlc_rightPath_arcSeparatingSet hn gamma

/--
[rlc_swappedBelowSet_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_swappedBelowSet_spec_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  (∀ z : Site 2, z ∈ rect (-n) n 0 (2 * n) → z 0 = -n → z ∈ rlc_swappedBelowSet hn gamma) ∧ (∀ z : Site 2, z ∈ rect (-n) n 0 (2 * n) → z 0 = n → z ∉ rlc_swappedBelowSet hn gamma) ∧ (∀ u v : Site 2, u ∈ rect (-n) n 0 (2 * n) → v ∈ rect (-n) n 0 (2 * n) → (hypercubicLattice 2).Adj u v → bdEdge (rlc_swappedBelowSet hn gamma) s(u, v) → u ∈ rlc_swappedRightPathSupport gamma ∨ v ∈ rlc_swappedRightPathSupport gamma) := by
-- proof
  apply StatMech.Universality.rlc_swappedBelowSet_spec hn gamma

/--
[rlc_bottomSide_subset_belowSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_bottomSide_subset_belowSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  bottomSide 0 (2 * n) (-n) n ⊆ rlc_belowSet hn gamma := by
-- proof
  apply StatMech.Universality.rlc_bottomSide_subset_belowSet hn gamma

/--
[rlc_topSide_disjoint_belowSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_topSide_disjoint_belowSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  Disjoint (topSide 0 (2 * n) (-n) n) (rlc_belowSet hn gamma) := by
-- proof
  apply StatMech.Universality.rlc_topSide_disjoint_belowSet hn gamma

/--
[rlc_leftPath_arcSeparatingSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPath_arcSeparatingSet_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  ArcSeparatingSet (rlc_swappedLeftPathSupport gamma) (-n) n (-2 * n) 0 := by
-- proof
  apply StatMech.Universality.rlc_leftPath_arcSeparatingSet hn gamma

/--
[rlc_swappedLeftBelowSet_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_swappedLeftBelowSet_spec_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  (∀ z : Site 2, z ∈ rect (-n) n (-2 * n) 0 → z 0 = -n → z ∈ rlc_swappedLeftBelowSet hn gamma) ∧ (∀ z : Site 2, z ∈ rect (-n) n (-2 * n) 0 → z 0 = n → z ∉ rlc_swappedLeftBelowSet hn gamma) ∧ (∀ u v : Site 2, u ∈ rect (-n) n (-2 * n) 0 → v ∈ rect (-n) n (-2 * n) 0 → (hypercubicLattice 2).Adj u v → bdEdge (rlc_swappedLeftBelowSet hn gamma) s(u, v) → u ∈ rlc_swappedLeftPathSupport gamma ∨ v ∈ rlc_swappedLeftPathSupport gamma) := by
-- proof
  apply StatMech.Universality.rlc_swappedLeftBelowSet_spec hn gamma

/--
[rlc_leftTopSide_subset_aboveSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftTopSide_subset_aboveSet_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  topSide (-2 * n) 0 (-n) n ⊆ rlc_aboveSet hn gamma := by
-- proof
  apply StatMech.Universality.rlc_leftTopSide_subset_aboveSet hn gamma

/--
[rlc_leftBottomSide_disjoint_aboveSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftBottomSide_disjoint_aboveSet_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  Disjoint (bottomSide (-2 * n) 0 (-n) n) (rlc_aboveSet hn gamma) := by
-- proof
  apply StatMech.Universality.rlc_leftBottomSide_disjoint_aboveSet hn gamma

/--
[rlc_half_rightDiagonal_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_half_rightDiagonal_lower_bound_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hH : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) (-n) n))
  (hV : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 (2 * n) (-n) n)) :
-- imply
  (1 : ℝ) / 32 ≤ rba_selfDualMeasure.real (rlc_rightDiagonal n) := by
-- proof
  apply StatMech.Universality.rlc_half_rightDiagonal_lower_bound n hn hH hV

/--
[rlc_half_leftDiagonal_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_half_leftDiagonal_lower_bound_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hH : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) (-n) n))
  (hV : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 (2 * n) (-n) n)) :
-- imply
  (1 : ℝ) / 32 ≤ rba_selfDualMeasure.real (rlc_leftDiagonal n) := by
-- proof
  apply StatMech.Universality.rlc_half_leftDiagonal_lower_bound n hn hH hV

/--
[rlc_lrRestricted_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_lrRestricted_univ_eq
  {a b c d : ℤ} :
-- imply
  rlc_lrRestrictedEvent a b c d Set.univ Set.univ = horizontalCrossingEvent a b c d := by
-- proof
  apply StatMech.Universality.rlc_lrRestricted_univ a b c d

/--
[rlc_horizontalCrossing_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_horizontalCrossing_dependsOn_eq
  {a b c d : ℤ} :
-- imply
  DependsOn ((horizontalCrossingEvent a b c d).indicator (fun _ => (1 : ℝ))) (edgesWithinFinset (rect_finite a b c d).toFinset : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_horizontalCrossing_dependsOn a b c d

/--
[rlc_horizontalCrossing_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_horizontalCrossing_measurableSet_eq
  {a b c d : ℤ} :
-- imply
  MeasurableSet (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rlc_horizontalCrossing_measurableSet a b c d

/--
[rlc_verticalCrossing_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_verticalCrossing_measurableSet_eq
  {a b c d : ℤ} :
-- imply
  MeasurableSet (verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rlc_verticalCrossing_measurableSet a b c d

/--
[rlc_square_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_square_half_eq
  {m : ℤ}
-- given
  (hm : 0 < m) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 m 0 m) := by
-- proof
  apply StatMech.Universality.rlc_square_half m hm

/--
[rlc_centered_square_horizontal_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_centered_square_horizontal_half_eq
  {n : ℤ}
-- given
  (hn : 0 < n) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) (-n) n) := by
-- proof
  apply StatMech.Universality.rlc_centered_square_horizontal_half n hn

/--
[rlc_centered_square_vertical_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_centered_square_vertical_half_eq
  {n : ℤ}
-- given
  (hn : 0 < n) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 (2 * n) (-n) n) := by
-- proof
  apply StatMech.Universality.rlc_centered_square_vertical_half n hn

/--
[rlc_half_rightDiagonal_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_half_rightDiagonal_unconditional_eq
  {n : ℤ}
-- given
  (hn : 0 < n) :
-- imply
  (1 : ℝ) / 32 ≤ rba_selfDualMeasure.real (rlc_rightDiagonal n) := by
-- proof
  apply StatMech.Universality.rlc_half_rightDiagonal_unconditional n hn

/--
[rlc_half_leftDiagonal_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_half_leftDiagonal_unconditional_eq
  {n : ℤ}
-- given
  (hn : 0 < n) :
-- imply
  (1 : ℝ) / 32 ≤ rba_selfDualMeasure.real (rlc_leftDiagonal n) := by
-- proof
  apply StatMech.Universality.rlc_half_leftDiagonal_unconditional n hn

/--
[rlc_pathVertices_rot180RightPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathVertices_rot180RightPath_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  rlc_pathVertices (rlc_rot180RightPath gamma).1 = (rlc_pathVertices gamma.1).image rlc_rot180 := by
-- proof
  apply StatMech.Universality.rlc_pathVertices_rot180RightPath gamma

/--
[rlc_pathVertices_rot180LeftPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathVertices_rot180LeftPath_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  rlc_pathVertices (rlc_rot180LeftPath gamma).1 = (rlc_pathVertices gamma.1).image rlc_rot180 := by
-- proof
  apply StatMech.Universality.rlc_pathVertices_rot180LeftPath gamma

/--
[rlc_pathVertices_rot180_roundtrip_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathVertices_rot180_roundtrip_left_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  rlc_pathVertices (rlc_rot180RightPath (rlc_rot180LeftPath gamma)).1 = rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_pathVertices_rot180_roundtrip_left gamma

/--
[rlc_pathVertices_rot180_roundtrip_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathVertices_rot180_roundtrip_right_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  rlc_pathVertices (rlc_rot180LeftPath (rlc_rot180RightPath gamma)).1 = rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_pathVertices_rot180_roundtrip_right gamma

/--
[rlc_pathEdges_rot180RightPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathEdges_rot180RightPath_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  rlc_pathEdges (rlc_rot180RightPath gamma).1 = (rlc_pathEdges gamma.1).image (Sym2.map rlc_rot180) := by
-- proof
  apply StatMech.Universality.rlc_pathEdges_rot180RightPath gamma

/--
[rlc_pathEdges_rot180LeftPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathEdges_rot180LeftPath_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  rlc_pathEdges (rlc_rot180LeftPath gamma).1 = (rlc_pathEdges gamma.1).image (Sym2.map rlc_rot180) := by
-- proof
  apply StatMech.Universality.rlc_pathEdges_rot180LeftPath gamma

/--
[rlc_pathEdges_rot180_roundtrip_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathEdges_rot180_roundtrip_left_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  rlc_pathEdges (rlc_rot180RightPath (rlc_rot180LeftPath gamma)).1 = rlc_pathEdges gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_pathEdges_rot180_roundtrip_left gamma

/--
[rlc_swappedRightPathSupport_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_swappedRightPathSupport_eq_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  rlc_swappedRightPathSupport gamma = crf_swap '' (rlc_pathVertices gamma.1 : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_swappedRightPathSupport_eq gamma

/--
[rlc_swappedLeftPathSupport_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_swappedLeftPathSupport_eq_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  rlc_swappedLeftPathSupport gamma = crf_swap '' (rlc_pathVertices gamma.1 : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_swappedLeftPathSupport_eq gamma

/--
[rlc_belowSet_boundary_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_belowSet_boundary_path_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (hn : 0 < n)
  (hu : u ∈ rect 0 (2 * n) (-n) n)
  (hv : v ∈ rect 0 (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (rlc_belowSet hn gamma) s(u, v)) :
-- imply
  u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_belowSet_boundary_path hn gamma hu hv hadj hbd

/--
[rlc_aboveSet_boundary_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_aboveSet_boundary_path_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
  {u v : Site 2}
-- given
  (hn : 0 < n)
  (hu : u ∈ rect (-2 * n) 0 (-n) n)
  (hv : v ∈ rect (-2 * n) 0 (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (rlc_aboveSet hn gamma) s(u, v)) :
-- imply
  u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_aboveSet_boundary_path hn gamma hu hv hadj hbd

/--
[rlc_rightPathAvoidGraph_walk_dest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathAvoidGraph_walk_dest_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {x z : Site 2}
  {w : (rlc_rightPathAvoidGraph gamma).Walk x z}
-- given
  (hxR : x ∈ rect 0 (2 * n) (-n) n)
  (hxP : x ∉ rlc_pathVertices gamma.1) :
-- imply
  z ∈ rect 0 (2 * n) (-n) n ∧ z ∉ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_rightPathAvoidGraph_walk_dest gamma hxR hxP w

/--
[rlc_strictTopSet_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictTopSet_subset_box_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  rlc_strictTopSet gamma ⊆ rect 0 (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_strictTopSet_subset_box gamma

/--
[rlc_strictTopSet_disjoint_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictTopSet_disjoint_path_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  Disjoint (rlc_strictTopSet gamma) (rlc_pathVertices gamma.1 : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_strictTopSet_disjoint_path gamma

/--
[rlc_strictTopSet_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictTopSet_step_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_strictTopSet gamma)
  (hvR : v ∈ rect 0 (2 * n) (-n) n)
  (hvp : v ∉ rlc_pathVertices gamma.1)
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  v ∈ rlc_strictTopSet gamma := by
-- proof
  apply StatMech.Universality.rlc_strictTopSet_step gamma hu hvR hvp hadj

/--
[rlc_strictTopSet_boundary_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictTopSet_boundary_path_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (huR : u ∈ rect 0 (2 * n) (-n) n)
  (hvR : v ∈ rect 0 (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (rlc_strictTopSet gamma) s(u, v)) :
-- imply
  u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_strictTopSet_boundary_path gamma huR hvR hadj hbd

/--
[rlc_strictTopSet_mono_of_disjoint_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictTopSet_mono_of_disjoint_path_eq
  {n : ℤ}
  {gamma lambda : RlcRightDiagonalPath n}
-- given
  (hdisj : Disjoint (rlc_strictTopSet gamma) (rlc_pathVertices lambda.1 : Set (Site 2))) :
-- imply
  rlc_strictTopSet gamma ⊆ rlc_strictTopSet lambda := by
-- proof
  apply StatMech.Universality.rlc_strictTopSet_mono_of_disjoint_path gamma lambda hdisj

/--
[rlc_strictBelowSet_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBelowSet_subset_box_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  rlc_strictBelowSet gamma ⊆ rect 0 (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_strictBelowSet_subset_box gamma

/--
[rlc_strictBelowSet_disjoint_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBelowSet_disjoint_path_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  Disjoint (rlc_strictBelowSet gamma) (rlc_pathVertices gamma.1 : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_strictBelowSet_disjoint_path gamma

/--
[rlc_strictBelowSet_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBelowSet_step_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_strictBelowSet gamma)
  (hvR : v ∈ rect 0 (2 * n) (-n) n)
  (hvp : v ∉ rlc_pathVertices gamma.1)
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  v ∈ rlc_strictBelowSet gamma := by
-- proof
  apply StatMech.Universality.rlc_strictBelowSet_step gamma hu hvR hvp hadj

/--
[rlc_strictBelowSet_mono_of_disjoint_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBelowSet_mono_of_disjoint_path_eq
  {n : ℤ}
  {gamma lambda : RlcRightDiagonalPath n}
-- given
  (hdisj : Disjoint (rlc_strictBelowSet gamma) (rlc_pathVertices lambda.1 : Set (Site 2))) :
-- imply
  rlc_strictBelowSet gamma ⊆ rlc_strictBelowSet lambda := by
-- proof
  apply StatMech.Universality.rlc_strictBelowSet_mono_of_disjoint_path gamma lambda hdisj

/--
[rlc_strictBelowSet_boundary_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBelowSet_boundary_path_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (huR : u ∈ rect 0 (2 * n) (-n) n)
  (hvR : v ∈ rect 0 (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (rlc_strictBelowSet gamma) s(u, v)) :
-- imply
  u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_strictBelowSet_boundary_path gamma huR hvR hadj hbd

/--
[rlc_topSide_disjoint_strictBelowSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_topSide_disjoint_strictBelowSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  Disjoint (topSide 0 (2 * n) (-n) n) (rlc_strictBelowSet gamma) := by
-- proof
  apply StatMech.Universality.rlc_topSide_disjoint_strictBelowSet hn gamma

/--
[rlc_strictBelowSet_subset_belowSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBelowSet_subset_belowSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  rlc_strictBelowSet gamma ⊆ rlc_belowSet hn gamma := by
-- proof
  apply StatMech.Universality.rlc_strictBelowSet_subset_belowSet hn gamma

/--
[rlc_strictTopSet_disjoint_belowSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictTopSet_disjoint_belowSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  Disjoint (rlc_strictTopSet gamma) (rlc_belowSet hn gamma) := by
-- proof
  apply StatMech.Universality.rlc_strictTopSet_disjoint_belowSet hn gamma

/--
[rlc_strictTopSet_disjoint_strictBelowSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictTopSet_disjoint_strictBelowSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  Disjoint (rlc_strictTopSet gamma) (rlc_strictBelowSet gamma) := by
-- proof
  apply StatMech.Universality.rlc_strictTopSet_disjoint_strictBelowSet hn gamma

/--
[rlc_disjointRightPaths_not_mutually_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_disjointRightPaths_not_mutually_top_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n)
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1)) :
-- imply
  ¬ ((rlc_pathVertices gamma.1 : Set (Site 2)) ⊆ rlc_strictTopSet delta ∧ (rlc_pathVertices delta.1 : Set (Site 2)) ⊆ rlc_strictTopSet gamma) := by
-- proof
  apply StatMech.Universality.rlc_disjointRightPaths_not_mutually_top hn gamma delta hdisj

/--
[rlc_leftPathAvoidGraph_walk_dest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathAvoidGraph_walk_dest_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
  {x z : Site 2}
  {w : (rlc_leftPathAvoidGraph gamma).Walk x z}
-- given
  (hxR : x ∈ rect (-2 * n) 0 (-n) n)
  (hxP : x ∉ rlc_pathVertices gamma.1) :
-- imply
  z ∈ rect (-2 * n) 0 (-n) n ∧ z ∉ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_leftPathAvoidGraph_walk_dest gamma hxR hxP w

/--
[rlc_strictBottomSet_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBottomSet_subset_box_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  rlc_strictBottomSet gamma ⊆ rect (-2 * n) 0 (-n) n := by
-- proof
  apply StatMech.Universality.rlc_strictBottomSet_subset_box gamma

/--
[rlc_strictBottomSet_disjoint_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBottomSet_disjoint_path_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  Disjoint (rlc_strictBottomSet gamma) (rlc_pathVertices gamma.1 : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_strictBottomSet_disjoint_path gamma

/--
[rlc_strictBottomSet_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBottomSet_step_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_strictBottomSet gamma)
  (hvR : v ∈ rect (-2 * n) 0 (-n) n)
  (hvp : v ∉ rlc_pathVertices gamma.1)
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  v ∈ rlc_strictBottomSet gamma := by
-- proof
  apply StatMech.Universality.rlc_strictBottomSet_step gamma hu hvR hvp hadj

/--
[rlc_strictBottomSet_boundary_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBottomSet_boundary_path_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
  {u v : Site 2}
-- given
  (huR : u ∈ rect (-2 * n) 0 (-n) n)
  (hvR : v ∈ rect (-2 * n) 0 (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (rlc_strictBottomSet gamma) s(u, v)) :
-- imply
  u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_strictBottomSet_boundary_path gamma huR hvR hadj hbd

/--
[rlc_strictTopSet_eq_of_pathVertices_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictTopSet_eq_of_pathVertices_eq_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hverts : rlc_pathVertices gamma.1 = rlc_pathVertices delta.1) :
-- imply
  rlc_strictTopSet gamma = rlc_strictTopSet delta := by
-- proof
  apply StatMech.Universality.rlc_strictTopSet_eq_of_pathVertices_eq gamma delta hverts

/--
[rlc_strictBottomSet_eq_of_pathVertices_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBottomSet_eq_of_pathVertices_eq_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n}
-- given
  (hverts : rlc_pathVertices gamma.1 = rlc_pathVertices delta.1) :
-- imply
  rlc_strictBottomSet gamma = rlc_strictBottomSet delta := by
-- proof
  apply StatMech.Universality.rlc_strictBottomSet_eq_of_pathVertices_eq gamma delta hverts

/--
[rlc_rot180_mem_strictBottom_of_mem_strictTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rot180_mem_strictBottom_of_mem_strictTop_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_strictTopSet gamma) :
-- imply
  rlc_rot180 z ∈ rlc_strictBottomSet (rlc_rot180RightPath gamma) := by
-- proof
  apply StatMech.Universality.rlc_rot180_mem_strictBottom_of_mem_strictTop gamma hz

/--
[rlc_rot180_mem_strictTop_of_mem_strictBottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rot180_mem_strictTop_of_mem_strictBottom_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_strictBottomSet gamma) :
-- imply
  rlc_rot180 z ∈ rlc_strictTopSet (rlc_rot180LeftPath gamma) := by
-- proof
  apply StatMech.Universality.rlc_rot180_mem_strictTop_of_mem_strictBottom gamma hz

/--
[rlc_rot180_mem_strictBottom_iff_mem_strictTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rot180_mem_strictBottom_iff_mem_strictTop_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {z : Site 2} :
-- imply
  rlc_rot180 z ∈ rlc_strictBottomSet (rlc_rot180RightPath gamma) ↔ z ∈ rlc_strictTopSet gamma := by
-- proof
  apply StatMech.Universality.rlc_rot180_mem_strictBottom_iff_mem_strictTop gamma z

/--
[rlc_rot180_mem_strictTop_iff_mem_strictBottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rot180_mem_strictTop_iff_mem_strictBottom_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
  {z : Site 2} :
-- imply
  rlc_rot180 z ∈ rlc_strictTopSet (rlc_rot180LeftPath gamma) ↔ z ∈ rlc_strictBottomSet gamma := by
-- proof
  apply StatMech.Universality.rlc_rot180_mem_strictTop_iff_mem_strictBottom gamma z

/--
[rlc_strictBottomSet_mono_of_disjoint_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBottomSet_mono_of_disjoint_path_eq
  {n : ℤ}
  {gamma lambda : RlcLeftDiagonalPath n}
-- given
  (hdisj : Disjoint (rlc_strictBottomSet gamma) (rlc_pathVertices lambda.1 : Set (Site 2))) :
-- imply
  rlc_strictBottomSet gamma ⊆ rlc_strictBottomSet lambda := by
-- proof
  apply StatMech.Universality.rlc_strictBottomSet_mono_of_disjoint_path gamma lambda hdisj

/--
[rlc_strictAboveSet_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictAboveSet_subset_box_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  rlc_strictAboveSet gamma ⊆ rect (-2 * n) 0 (-n) n := by
-- proof
  apply StatMech.Universality.rlc_strictAboveSet_subset_box gamma

/--
[rlc_strictAboveSet_disjoint_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictAboveSet_disjoint_path_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  Disjoint (rlc_strictAboveSet gamma) (rlc_pathVertices gamma.1 : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_strictAboveSet_disjoint_path gamma

/--
[rlc_strictAboveSet_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictAboveSet_step_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_strictAboveSet gamma)
  (hvR : v ∈ rect (-2 * n) 0 (-n) n)
  (hvp : v ∉ rlc_pathVertices gamma.1)
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  v ∈ rlc_strictAboveSet gamma := by
-- proof
  apply StatMech.Universality.rlc_strictAboveSet_step gamma hu hvR hvp hadj

/--
[rlc_strictAboveSet_boundary_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictAboveSet_boundary_path_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
  {u v : Site 2}
-- given
  (huR : u ∈ rect (-2 * n) 0 (-n) n)
  (hvR : v ∈ rect (-2 * n) 0 (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (rlc_strictAboveSet gamma) s(u, v)) :
-- imply
  u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_strictAboveSet_boundary_path gamma huR hvR hadj hbd

/--
[rlc_leftBottomSide_disjoint_strictAboveSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftBottomSide_disjoint_strictAboveSet_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  Disjoint (bottomSide (-2 * n) 0 (-n) n) (rlc_strictAboveSet gamma) := by
-- proof
  apply StatMech.Universality.rlc_leftBottomSide_disjoint_strictAboveSet hn gamma

/--
[rlc_strictAboveSet_subset_aboveSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictAboveSet_subset_aboveSet_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  rlc_strictAboveSet gamma ⊆ rlc_aboveSet hn gamma := by
-- proof
  apply StatMech.Universality.rlc_strictAboveSet_subset_aboveSet hn gamma

/--
[rlc_strictBottomSet_disjoint_aboveSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBottomSet_disjoint_aboveSet_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  Disjoint (rlc_strictBottomSet gamma) (rlc_aboveSet hn gamma) := by
-- proof
  apply StatMech.Universality.rlc_strictBottomSet_disjoint_aboveSet hn gamma

/--
[rlc_strictBottomSet_disjoint_strictAboveSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBottomSet_disjoint_strictAboveSet_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  Disjoint (rlc_strictBottomSet gamma) (rlc_strictAboveSet gamma) := by
-- proof
  apply StatMech.Universality.rlc_strictBottomSet_disjoint_strictAboveSet hn gamma

/--
[rlc_strictBelowSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBelowSet_finite_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  (rlc_strictBelowSet gamma).Finite := by
-- proof
  apply StatMech.Universality.rlc_strictBelowSet_finite gamma

/--
[rlc_strictAboveSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictAboveSet_finite_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  (rlc_strictAboveSet gamma).Finite := by
-- proof
  apply StatMech.Universality.rlc_strictAboveSet_finite gamma

/--
[rlc_strictTopSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictTopSet_finite_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  (rlc_strictTopSet gamma).Finite := by
-- proof
  apply StatMech.Universality.rlc_strictTopSet_finite gamma

/--
[rlc_strictBottomSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBottomSet_finite_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  (rlc_strictBottomSet gamma).Finite := by
-- proof
  apply StatMech.Universality.rlc_strictBottomSet_finite gamma

/--
[rlc_bdEdge_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_bdEdge_inter_eq
  {S T : Set (Site 2)}
  {e : Sym2 (Site 2)}
-- given
  (h : bdEdge (S ∩ T) e) :
-- imply
  bdEdge S e ∨ bdEdge T e := by
-- proof
  apply StatMech.Universality.rlc_bdEdge_inter h

/--
[rlc_bdEdge_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_bdEdge_union_eq
  {S T : Set (Site 2)}
  {e : Sym2 (Site 2)}
-- given
  (h : bdEdge (S ∪ T) e) :
-- imply
  bdEdge S e ∨ bdEdge T e := by
-- proof
  apply StatMech.Universality.rlc_bdEdge_union h

/--
[rlc_rightUpperUnionSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightUpperUnionSet_finite_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  (rlc_rightUpperUnionSet gamma delta).Finite := by
-- proof
  apply StatMech.Universality.rlc_rightUpperUnionSet_finite gamma delta

/--
[rlc_rightUpperUnionSet_boundary_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightUpperUnionSet_boundary_paths_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (huR : u ∈ rect 0 (2 * n) (-n) n)
  (hvR : v ∈ rect 0 (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (rlc_rightUpperUnionSet gamma delta) s(u, v)) :
-- imply
  (u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1) ∨ (u ∈ rlc_pathVertices delta.1 ∨ v ∈ rlc_pathVertices delta.1) := by
-- proof
  apply StatMech.Universality.rlc_rightUpperUnionSet_boundary_paths gamma delta huR hvR hadj hbd

/--
[rlc_rightUpperUnionSet_exit_mem_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightUpperUnionSet_exit_mem_paths_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_rightUpperUnionSet gamma delta)
  (hvR : v ∈ rect 0 (2 * n) (-n) n)
  (hv : v ∉ rlc_rightUpperUnionSet gamma delta)
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  v ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_rightUpperUnionSet_exit_mem_paths gamma delta hu hvR hv hadj

/--
[rlc_leftLowerUnionSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftLowerUnionSet_finite_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n} :
-- imply
  (rlc_leftLowerUnionSet gamma delta).Finite := by
-- proof
  apply StatMech.Universality.rlc_leftLowerUnionSet_finite gamma delta

/--
[rlc_leftLowerUnionSet_boundary_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftLowerUnionSet_boundary_paths_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n}
  {u v : Site 2}
-- given
  (huR : u ∈ rect (-2 * n) 0 (-n) n)
  (hvR : v ∈ rect (-2 * n) 0 (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (rlc_leftLowerUnionSet gamma delta) s(u, v)) :
-- imply
  (u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1) ∨ (u ∈ rlc_pathVertices delta.1 ∨ v ∈ rlc_pathVertices delta.1) := by
-- proof
  apply StatMech.Universality.rlc_leftLowerUnionSet_boundary_paths gamma delta huR hvR hadj hbd

/--
[rlc_leftLowerUnionSet_exit_mem_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftLowerUnionSet_exit_mem_paths_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_leftLowerUnionSet gamma delta)
  (hvR : v ∈ rect (-2 * n) 0 (-n) n)
  (hv : v ∉ rlc_leftLowerUnionSet gamma delta)
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  v ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_leftLowerUnionSet_exit_mem_paths gamma delta hu hvR hv hadj

/--
[rlc_commonStrictBelowSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_commonStrictBelowSet_finite_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  (rlc_commonStrictBelowSet gamma delta).Finite := by
-- proof
  apply StatMech.Universality.rlc_commonStrictBelowSet_finite gamma delta

/--
[rlc_bottom_mem_commonStrictBelowSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_bottom_mem_commonStrictBelowSet_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ bottomSide 0 (2 * n) (-n) n)
  (hgamma : z ∉ rlc_pathVertices gamma.1)
  (hdelta : z ∉ rlc_pathVertices delta.1) :
-- imply
  z ∈ rlc_commonStrictBelowSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_bottom_mem_commonStrictBelowSet gamma delta hz hgamma hdelta

/--
[rlc_topSide_disjoint_commonStrictBelowSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_topSide_disjoint_commonStrictBelowSet_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  Disjoint (topSide 0 (2 * n) (-n) n) (rlc_commonStrictBelowSet gamma delta) := by
-- proof
  apply StatMech.Universality.rlc_topSide_disjoint_commonStrictBelowSet hn gamma delta

/--
[rlc_commonStrictBelowSet_boundary_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_commonStrictBelowSet_boundary_paths_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (huR : u ∈ rect 0 (2 * n) (-n) n)
  (hvR : v ∈ rect 0 (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (rlc_commonStrictBelowSet gamma delta) s(u, v)) :
-- imply
  (u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1) ∨ (u ∈ rlc_pathVertices delta.1 ∨ v ∈ rlc_pathVertices delta.1) := by
-- proof
  apply StatMech.Universality.rlc_commonStrictBelowSet_boundary_paths gamma delta huR hvR hadj hbd

/--
[rlc_rightPairAvoidGraph_walk_dest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPairAvoidGraph_walk_dest_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {x z : Site 2}
  {w : (rlc_rightPairAvoidGraph gamma delta).Walk x z}
-- given
  (hxR : x ∈ rect 0 (2 * n) (-n) n)
  (hxGamma : x ∉ rlc_pathVertices gamma.1)
  (hxDelta : x ∉ rlc_pathVertices delta.1) :
-- imply
  z ∈ rect 0 (2 * n) (-n) n ∧ z ∉ rlc_pathVertices gamma.1 ∧ z ∉ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_rightPairAvoidGraph_walk_dest gamma delta hxR hxGamma hxDelta w

/--
[rlc_jointBottomSet_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomSet_subset_box_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  rlc_jointBottomSet gamma delta ⊆ rect 0 (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_jointBottomSet_subset_box gamma delta

/--
[rlc_jointBottomSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomSet_finite_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  (rlc_jointBottomSet gamma delta).Finite := by
-- proof
  apply StatMech.Universality.rlc_jointBottomSet_finite gamma delta

/--
[rlc_jointBottomSet_disjoint_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomSet_disjoint_paths_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  Disjoint (rlc_jointBottomSet gamma delta) ((rlc_pathVertices gamma.1 : Set (Site 2)) ∪ rlc_pathVertices delta.1) := by
-- proof
  apply StatMech.Universality.rlc_jointBottomSet_disjoint_paths gamma delta

/--
[rlc_jointBottomSet_subset_commonStrictBelowSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomSet_subset_commonStrictBelowSet_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  rlc_jointBottomSet gamma delta ⊆ rlc_commonStrictBelowSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_jointBottomSet_subset_commonStrictBelowSet gamma delta

/--
[rlc_jointBottomSet_exit_mem_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomSet_exit_mem_paths_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_jointBottomSet gamma delta)
  (hvR : v ∈ rect 0 (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hv : v ∉ rlc_jointBottomSet gamma delta) :
-- imply
  v ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_jointBottomSet_exit_mem_paths gamma delta hu hvR hadj hv

/--
[rlc_jointBottomSet_boundary_trace_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomSet_boundary_trace_safe_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (hn : 0 < n)
  (hu : u ∈ rlc_jointBottomSet gamma delta)
  (hvR : v ∈ rect 0 (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hvPath : v ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices delta.1) :
-- imply
  v ∉ rlc_rightUpperUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_jointBottomSet_boundary_trace_safe hn gamma delta hu hvR hadj hvPath

/--
[rlc_jointBottomSet_exit_mem_paths_and_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomSet_exit_mem_paths_and_safe_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (hn : 0 < n)
  (hu : u ∈ rlc_jointBottomSet gamma delta)
  (hvR : v ∈ rect 0 (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hv : v ∉ rlc_jointBottomSet gamma delta) :
-- imply
  (v ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices delta.1) ∧ v ∉ rlc_rightUpperUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_jointBottomSet_exit_mem_paths_and_safe hn gamma delta hu hvR hadj hv

/--
[rlc_jointBottomTraceBoundary_subset_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomTraceBoundary_subset_paths_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  rlc_jointBottomTraceBoundary gamma delta ⊆ (rlc_pathVertices gamma.1 : Set (Site 2)) ∪ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_jointBottomTraceBoundary_subset_paths gamma delta

/--
[rlc_jointBottomTraceBoundary_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomTraceBoundary_finite_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  (rlc_jointBottomTraceBoundary gamma delta).Finite := by
-- proof
  apply StatMech.Universality.rlc_jointBottomTraceBoundary_finite gamma delta

/--
[rlc_jointBottomTraceBoundary_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomTraceBoundary_safe_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {v : Site 2}
-- given
  (hn : 0 < n)
  (hv : v ∈ rlc_jointBottomTraceBoundary gamma delta) :
-- imply
  v ∉ rlc_rightUpperUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_jointBottomTraceBoundary_safe hn gamma delta hv

/--
[rlc_bottomTraceVertex_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_bottomTraceVertex_safe_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {v : Site 2}
-- given
  (hn : 0 < n)
  (hvBottom : v ∈ bottomSide 0 (2 * n) (-n) n)
  (_hvPath : v ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices delta.1) :
-- imply
  v ∉ rlc_rightUpperUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_bottomTraceVertex_safe hn gamma delta hvBottom _hvPath

/--
[rlc_jointBottomTraceFrontier_subset_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomTraceFrontier_subset_paths_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  rlc_jointBottomTraceFrontier gamma delta ⊆ (rlc_pathVertices gamma.1 : Set (Site 2)) ∪ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_jointBottomTraceFrontier_subset_paths gamma delta

/--
[rlc_jointBottomTraceFrontier_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomTraceFrontier_finite_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  (rlc_jointBottomTraceFrontier gamma delta).Finite := by
-- proof
  apply StatMech.Universality.rlc_jointBottomTraceFrontier_finite gamma delta

/--
[rlc_jointBottomTraceFrontier_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomTraceFrontier_safe_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {v : Site 2}
-- given
  (hn : 0 < n)
  (hv : v ∈ rlc_jointBottomTraceFrontier gamma delta) :
-- imply
  v ∉ rlc_rightUpperUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_jointBottomTraceFrontier_safe hn gamma delta hv

/--
[rlc_commonStrictAboveSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_commonStrictAboveSet_finite_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n} :
-- imply
  (rlc_commonStrictAboveSet gamma delta).Finite := by
-- proof
  apply StatMech.Universality.rlc_commonStrictAboveSet_finite gamma delta

/--
[rlc_top_mem_commonStrictAboveSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_top_mem_commonStrictAboveSet_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ topSide (-2 * n) 0 (-n) n)
  (hgamma : z ∉ rlc_pathVertices gamma.1)
  (hdelta : z ∉ rlc_pathVertices delta.1) :
-- imply
  z ∈ rlc_commonStrictAboveSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_top_mem_commonStrictAboveSet gamma delta hz hgamma hdelta

/--
[rlc_leftBottomSide_disjoint_commonStrictAboveSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftBottomSide_disjoint_commonStrictAboveSet_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  Disjoint (bottomSide (-2 * n) 0 (-n) n) (rlc_commonStrictAboveSet gamma delta) := by
-- proof
  apply StatMech.Universality.rlc_leftBottomSide_disjoint_commonStrictAboveSet hn gamma delta

/--
[rlc_commonStrictAboveSet_boundary_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_commonStrictAboveSet_boundary_paths_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n}
  {u v : Site 2}
-- given
  (huR : u ∈ rect (-2 * n) 0 (-n) n)
  (hvR : v ∈ rect (-2 * n) 0 (-n) n)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (rlc_commonStrictAboveSet gamma delta) s(u, v)) :
-- imply
  (u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1) ∨ (u ∈ rlc_pathVertices delta.1 ∨ v ∈ rlc_pathVertices delta.1) := by
-- proof
  apply StatMech.Universality.rlc_commonStrictAboveSet_boundary_paths gamma delta huR hvR hadj hbd

/--
[rlc_mem_strictBelowVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_strictBelowVertices_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {z : Site 2} :
-- imply
  z ∈ rlc_strictBelowVertices gamma ↔ z ∈ rlc_strictBelowSet gamma := by
-- proof
  apply StatMech.Universality.rlc_mem_strictBelowVertices

/--
[rlc_mem_strictAboveVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_strictAboveVertices_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
  {z : Site 2} :
-- imply
  z ∈ rlc_strictAboveVertices gamma ↔ z ∈ rlc_strictAboveSet gamma := by
-- proof
  apply StatMech.Universality.rlc_mem_strictAboveVertices

/--
[rlc_mem_strictTopVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_strictTopVertices_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {z : Site 2} :
-- imply
  z ∈ rlc_strictTopVertices gamma ↔ z ∈ rlc_strictTopSet gamma := by
-- proof
  apply StatMech.Universality.rlc_mem_strictTopVertices

/--
[rlc_mem_strictBottomVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_strictBottomVertices_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
  {z : Site 2} :
-- imply
  z ∈ rlc_strictBottomVertices gamma ↔ z ∈ rlc_strictBottomSet gamma := by
-- proof
  apply StatMech.Universality.rlc_mem_strictBottomVertices

/--
[rlc_path_start_mem_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_path_start_mem_vertices_eq
  {a b c d : ℤ}
  {gamma : RlcCrossingPath a b c d} :
-- imply
  (gamma.1 : Site 2) ∈ rlc_pathVertices gamma := by
-- proof
  apply StatMech.Universality.rlc_path_start_mem_vertices gamma

/--
[rlc_rightPathStrictlyBelow_irrefl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathStrictlyBelow_irrefl_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  ¬ rlc_rightPathStrictlyBelow gamma gamma := by
-- proof
  apply StatMech.Universality.rlc_rightPathStrictlyBelow_irrefl gamma

/--
[rlc_leftPathStrictlyAbove_irrefl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathStrictlyAbove_irrefl_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  ¬ rlc_leftPathStrictlyAbove gamma gamma := by
-- proof
  apply StatMech.Universality.rlc_leftPathStrictlyAbove_irrefl gamma

/--
[rlc_rightPathVertex_mem_explored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathVertex_mem_explored_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_pathVertices gamma.1) :
-- imply
  z ∈ rlc_rightExploredVertices gamma := by
-- proof
  apply StatMech.Universality.rlc_rightPathVertex_mem_explored gamma hz

/--
[rlc_leftPathVertex_mem_explored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathVertex_mem_explored_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_pathVertices gamma.1) :
-- imply
  z ∈ rlc_leftExploredVertices gamma := by
-- proof
  apply StatMech.Universality.rlc_leftPathVertex_mem_explored gamma hz

/--
[rlc_rightPathBelow_irrefl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathBelow_irrefl_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  ¬ rlc_rightPathBelow gamma gamma := by
-- proof
  apply StatMech.Universality.rlc_rightPathBelow_irrefl gamma

/--
[rlc_leftPathAbove_irrefl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathAbove_irrefl_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  ¬ rlc_leftPathAbove gamma gamma := by
-- proof
  apply StatMech.Universality.rlc_leftPathAbove_irrefl gamma

/--
[rlc_rightPathBelow_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathBelow_rank_lt_eq
  {n : ℤ}
  {delta gamma : RlcRightDiagonalPath n}
-- given
  (h : rlc_rightPathBelow delta gamma) :
-- imply
  rlc_rightPathRank delta < rlc_rightPathRank gamma := by
-- proof
  apply StatMech.Universality.rlc_rightPathBelow_rank_lt h

/--
[rlc_leftPathAbove_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathAbove_rank_lt_eq
  {n : ℤ}
  {delta gamma : RlcLeftDiagonalPath n}
-- given
  (h : rlc_leftPathAbove delta gamma) :
-- imply
  rlc_leftPathRank delta < rlc_leftPathRank gamma := by
-- proof
  apply StatMech.Universality.rlc_leftPathAbove_rank_lt h

/--
[rlc_pathEdge_endpoints_mem_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathEdge_endpoints_mem_vertices_eq
  {a b c d : ℤ}
  {gamma : RlcCrossingPath a b c d}
  {x y : Site 2}
-- given
  (he : s(x, y) ∈ rlc_pathEdges gamma) :
-- imply
  x ∈ rlc_pathVertices gamma ∧ y ∈ rlc_pathVertices gamma := by
-- proof
  apply StatMech.Universality.rlc_pathEdge_endpoints_mem_vertices gamma he

/--
[rlc_pathVertex_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathVertex_mem_rect_eq
  {a b c d : ℤ}
  {gamma : RlcCrossingPath a b c d}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_pathVertices gamma) :
-- imply
  z ∈ rect a b c d := by
-- proof
  apply StatMech.Universality.rlc_pathVertex_mem_rect gamma hz

/--
[rlc_rightSide_strictTop_height_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSide_strictTop_height_gt_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {z : rightSide 0 (2 * n) (-n) n}
-- given
  (hn : 0 < n)
  (hzTop : (z : Site 2) ∈ rlc_strictTopSet gamma) :
-- imply
  (gamma.1.2.1 : Site 2) 1 < (z : Site 2) 1 := by
-- proof
  apply StatMech.Universality.rlc_rightSide_strictTop_height_gt hn gamma z hzTop

/--
[rlc_right_endpoints_not_both_unsafe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_right_endpoints_not_both_unsafe_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  ¬ ((gamma.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta ∧ (delta.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta) := by
-- proof
  apply StatMech.Universality.rlc_right_endpoints_not_both_unsafe hn gamma delta

/--
[rlc_exists_safe_right_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_exists_safe_right_endpoint_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  (gamma.1.2.1 : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∨ (delta.1.2.1 : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_exists_safe_right_endpoint hn gamma delta

/--
[rlc_pathEdge_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathEdge_lattice_eq
  {a b c d : ℤ}
  {gamma : RlcCrossingPath a b c d}
  {x y : Site 2}
-- given
  (he : s(x, y) ∈ rlc_pathEdges gamma) :
-- imply
  (hypercubicLattice 2).Adj x y := by
-- proof
  apply StatMech.Universality.rlc_pathEdge_lattice gamma he

/--
[rlc_walk_pred_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_walk_pred_constant_eq
  {G : SimpleGraph V}
  {a b : V}
  {p : G.Walk a b}
  {z : V}
-- given
  (P : V → Prop)
  (hstep : ∀ {u v : V}, s(u, v) ∈ p.edges → (P u ↔ P v))
  (hz : z ∈ p.support) :
-- imply
  P z ↔ P a := by
-- proof
  apply StatMech.Universality.rlc_walk_pred_constant p P hstep hz

/--
[rlc_strictTopSet_mem_iff_walk_start_of_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictTopSet_mem_iff_walk_start_of_avoids_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {a b : Site 2}
  {p : (hypercubicLattice 2).Walk a b}
  {z : Site 2}
-- given
  (hbox : ∀ z ∈ p.support, z ∈ rect 0 (2 * n) (-n) n)
  (havoid : ∀ z ∈ p.support, z ∉ rlc_pathVertices gamma.1)
  (hz : z ∈ p.support) :
-- imply
  z ∈ rlc_strictTopSet gamma ↔ a ∈ rlc_strictTopSet gamma := by
-- proof
  apply StatMech.Universality.rlc_strictTopSet_mem_iff_walk_start_of_avoids gamma p hbox havoid hz

/--
[rlc_strictBelowSet_mem_iff_walk_start_of_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBelowSet_mem_iff_walk_start_of_avoids_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {a b : Site 2}
  {p : (hypercubicLattice 2).Walk a b}
  {z : Site 2}
-- given
  (hbox : ∀ z ∈ p.support, z ∈ rect 0 (2 * n) (-n) n)
  (havoid : ∀ z ∈ p.support, z ∉ rlc_pathVertices gamma.1)
  (hz : z ∈ p.support) :
-- imply
  z ∈ rlc_strictBelowSet gamma ↔ a ∈ rlc_strictBelowSet gamma := by
-- proof
  apply StatMech.Universality.rlc_strictBelowSet_mem_iff_walk_start_of_avoids gamma p hbox havoid hz

/--
[rlc_strictTopSet_mem_iff_rectWalk_start_of_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictTopSet_mem_iff_rectWalk_start_of_avoids_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {a b : rect 0 (2 * n) (-n) n}
  {p : ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)).Walk a b}
  {z : rect 0 (2 * n) (-n) n}
-- given
  (havoid : ∀ z ∈ p.support, (z : Site 2) ∉ rlc_pathVertices gamma.1)
  (hz : z ∈ p.support) :
-- imply
  (z : Site 2) ∈ rlc_strictTopSet gamma ↔ (a : Site 2) ∈ rlc_strictTopSet gamma := by
-- proof
  apply StatMech.Universality.rlc_strictTopSet_mem_iff_rectWalk_start_of_avoids gamma p havoid hz

/--
[rlc_strictBelowSet_mem_iff_rectWalk_start_of_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBelowSet_mem_iff_rectWalk_start_of_avoids_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {a b : rect 0 (2 * n) (-n) n}
  {p : ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)).Walk a b}
  {z : rect 0 (2 * n) (-n) n}
-- given
  (havoid : ∀ z ∈ p.support, (z : Site 2) ∉ rlc_pathVertices gamma.1)
  (hz : z ∈ p.support) :
-- imply
  (z : Site 2) ∈ rlc_strictBelowSet gamma ↔ (a : Site 2) ∈ rlc_strictBelowSet gamma := by
-- proof
  apply StatMech.Universality.rlc_strictBelowSet_mem_iff_rectWalk_start_of_avoids gamma p havoid hz

/--
[rlc_strictTopSet_mem_iff_path_start_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictTopSet_mem_iff_path_start_of_disjoint_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {z : Site 2}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1))
  (hz : z ∈ rlc_pathVertices delta.1) :
-- imply
  z ∈ rlc_strictTopSet gamma ↔ (delta.1.1 : Site 2) ∈ rlc_strictTopSet gamma := by
-- proof
  apply StatMech.Universality.rlc_strictTopSet_mem_iff_path_start_of_disjoint gamma delta hdisj hz

/--
[rlc_strictBottomSet_mem_iff_path_start_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_strictBottomSet_mem_iff_path_start_of_disjoint_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1))
  (hz : z ∈ rlc_pathVertices delta.1) :
-- imply
  z ∈ rlc_strictBottomSet gamma ↔ (delta.1.1 : Site 2) ∈ rlc_strictBottomSet gamma := by
-- proof
  apply StatMech.Universality.rlc_strictBottomSet_mem_iff_path_start_of_disjoint gamma delta hdisj hz

/--
[rlc_rightPathEdge_enter_strictTop_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathEdge_enter_strictTop_common_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (he : s(u, v) ∈ rlc_pathEdges gamma.1)
  (hu : u ∉ rlc_strictTopSet delta)
  (hv : v ∈ rlc_strictTopSet delta) :
-- imply
  u ∈ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_rightPathEdge_enter_strictTop_common gamma delta he hu hv

/--
[rlc_rightPathEdge_exit_strictTop_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathEdge_exit_strictTop_common_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (he : s(u, v) ∈ rlc_pathEdges gamma.1)
  (hu : u ∈ rlc_strictTopSet delta)
  (hv : v ∉ rlc_strictTopSet delta) :
-- imply
  v ∈ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_rightPathEdge_exit_strictTop_common gamma delta he hu hv

/--
[rlc_leftPathEdge_enter_strictBottom_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathEdge_enter_strictBottom_common_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n}
  {u v : Site 2}
-- given
  (he : s(u, v) ∈ rlc_pathEdges gamma.1)
  (hu : u ∉ rlc_strictBottomSet delta)
  (hv : v ∈ rlc_strictBottomSet delta) :
-- imply
  u ∈ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_leftPathEdge_enter_strictBottom_common gamma delta he hu hv

/--
[rlc_leftPathEdge_exit_strictBottom_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathEdge_exit_strictBottom_common_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n}
  {u v : Site 2}
-- given
  (he : s(u, v) ∈ rlc_pathEdges gamma.1)
  (hu : u ∈ rlc_strictBottomSet delta)
  (hv : v ∉ rlc_strictBottomSet delta) :
-- imply
  v ∈ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_leftPathEdge_exit_strictBottom_common gamma delta he hu hv

/--
[rlc_iUnion_rankedMinimalCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_iUnion_rankedMinimalCandidate_eq
  [Fintype I]
  {W : I → Set (ConfigSpace E)}
  {rank : I → ℕ}
-- given
  (prec : I → I → Prop)
  (hrank : ∀ {j i}, prec j i → rank j < rank i) :
-- imply
  (⋃ i, rlc_rankedMinimalCandidate W prec i) = ⋃ i, W i := by
-- proof
  apply StatMech.Universality.rlc_iUnion_rankedMinimalCandidate W prec rank hrank

/--
[rlc_mem_rightLowerPathEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_rightLowerPathEdges_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (hbelow : rlc_rightPathBelow delta gamma)
  (he : e ∈ rlc_pathEdges delta.1) :
-- imply
  e ∈ rlc_rightLowerPathEdges gamma := by
-- proof
  apply StatMech.Universality.rlc_mem_rightLowerPathEdges hbelow he

/--
[rlc_rightLowestCandidateEdges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightLowestCandidateEdges_subset_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  rlc_rightLowestCandidateEdges gamma ⊆ edgesWithinFinset (rlc_rightExploredVertices gamma) := by
-- proof
  apply StatMech.Universality.rlc_rightLowestCandidateEdges_subset gamma

/--
[rlc_rightLowestCandidate_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightLowestCandidate_dependsOn_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  DependsOn ((rlc_rightLowestCandidate gamma).indicator (fun _ => (1 : ℝ))) (rlc_rightLowestCandidateEdges gamma : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_rightLowestCandidate_dependsOn gamma

/--
[rlc_iUnion_rightLowestCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_iUnion_rightLowestCandidate_eq
  {n : ℤ} :
-- imply
  (⋃ gamma : RlcRightDiagonalPath n, rlc_rightLowestCandidate gamma) = rlc_rightDiagonal n := by
-- proof
  apply StatMech.Universality.rlc_iUnion_rightLowestCandidate n

/--
[rlc_mem_leftUpperPathEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_leftUpperPathEdges_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (habove : rlc_leftPathAbove delta gamma)
  (he : e ∈ rlc_pathEdges delta.1) :
-- imply
  e ∈ rlc_leftUpperPathEdges gamma := by
-- proof
  apply StatMech.Universality.rlc_mem_leftUpperPathEdges habove he

/--
[rlc_leftHighestCandidateEdges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftHighestCandidateEdges_subset_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  rlc_leftHighestCandidateEdges gamma ⊆ edgesWithinFinset (rlc_leftExploredVertices gamma) := by
-- proof
  apply StatMech.Universality.rlc_leftHighestCandidateEdges_subset gamma

/--
[rlc_leftHighestCandidate_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftHighestCandidate_dependsOn_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n} :
-- imply
  DependsOn ((rlc_leftHighestCandidate gamma).indicator (fun _ => (1 : ℝ))) (rlc_leftHighestCandidateEdges gamma : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_leftHighestCandidate_dependsOn gamma

/--
[rlc_iUnion_leftHighestCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_iUnion_leftHighestCandidate_eq
  {n : ℤ} :
-- imply
  (⋃ gamma : RlcLeftDiagonalPath n, rlc_leftHighestCandidate gamma) = rlc_leftDiagonal n := by
-- proof
  apply StatMech.Universality.rlc_iUnion_leftHighestCandidate n

/--
[rlc_extremalPairCandidate_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_extremalPairCandidate_dependsOn_eq
  {n : ℤ}
  {pair : RlcDiagonalPathPair n} :
-- imply
  DependsOn ((rlc_extremalPairCandidate pair).indicator (fun _ => (1 : ℝ))) (rlc_extremalPairCandidateEdges pair : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_extremalPairCandidate_dependsOn pair

/--
[rlc_extremalPairCandidate_subset_pathPairOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_extremalPairCandidate_subset_pathPairOpen_eq
  {n : ℤ}
  {pair : RlcDiagonalPathPair n} :
-- imply
  rlc_extremalPairCandidate pair ⊆ rlc_pathPairOpen pair := by
-- proof
  apply StatMech.Universality.rlc_extremalPairCandidate_subset_pathPairOpen pair

/--
[rlc_iUnion_extremalPairCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_iUnion_extremalPairCandidate_eq
  {n : ℤ} :
-- imply
  (⋃ pair : RlcDiagonalPathPair n, rlc_extremalPairCandidate pair) = rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
-- proof
  apply StatMech.Universality.rlc_iUnion_extremalPairCandidate n

/--
[rlc_rightLowestCandidate_not_open_of_below](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightLowestCandidate_not_open_of_below_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hgamma : omega ∈ rlc_rightLowestCandidate gamma)
  (hbelow : rlc_rightPathBelow delta gamma) :
-- imply
  omega ∉ rlc_pathOpen delta.1 := by
-- proof
  apply StatMech.Universality.rlc_rightLowestCandidate_not_open_of_below hgamma hbelow

/--
[rlc_leftHighestCandidate_not_open_of_above](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftHighestCandidate_not_open_of_above_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hgamma : omega ∈ rlc_leftHighestCandidate gamma)
  (habove : rlc_leftPathAbove delta gamma) :
-- imply
  omega ∉ rlc_pathOpen delta.1 := by
-- proof
  apply StatMech.Universality.rlc_leftHighestCandidate_not_open_of_above hgamma habove

/--
[rlc_rightTraceGraph_reachable_of_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightTraceGraph_reachable_of_common_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {z u v : rect 0 (2 * n) (-n) n}
-- given
  (hzGamma : z ∈ gamma.1.2.2.1.support)
  (hzDelta : z ∈ delta.1.2.2.1.support)
  (hu : u ∈ gamma.1.2.2.1.support)
  (hv : v ∈ delta.1.2.2.1.support) :
-- imply
  (rlc_rightTraceGraph gamma delta).Reachable u v := by
-- proof
  apply StatMech.Universality.rlc_rightTraceGraph_reachable_of_common gamma delta hzGamma hzDelta hu hv

/--
[rlc_rightSafeTraceGraph_le_traceGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceGraph_le_traceGraph_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  rlc_rightSafeTraceGraph gamma delta ≤ rlc_rightTraceGraph gamma delta := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceGraph_le_traceGraph gamma delta

/--
[rlc_jointBottomTraceBoundary_adj_safeTraceGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomTraceBoundary_adj_safeTraceGraph_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : rect 0 (2 * n) (-n) n}
-- given
  (hn : 0 < n)
  (hu : (u : Site 2) ∈ rlc_jointBottomTraceBoundary gamma delta)
  (hv : (v : Site 2) ∈ rlc_jointBottomTraceBoundary gamma delta)
  (he : s((u : Site 2), (v : Site 2)) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1)
  (hadj : ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)).Adj u v) :
-- imply
  (rlc_rightSafeTraceGraph gamma delta).Adj u v := by
-- proof
  apply StatMech.Universality.rlc_jointBottomTraceBoundary_adj_safeTraceGraph hn gamma delta hu hv he hadj

/--
[rlc_jointBottomTraceBoundary_walk_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomTraceBoundary_walk_safe_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {x y : rect 0 (2 * n) (-n) n}
  {w : (rlc_rightTraceGraph gamma delta).Walk x y}
-- given
  (hn : 0 < n)
  (hboundary : ∀ z ∈ w.support, (z : Site 2) ∈ rlc_jointBottomTraceBoundary gamma delta) :
-- imply
  (rlc_rightSafeTraceGraph gamma delta).Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_jointBottomTraceBoundary_walk_safe hn gamma delta w hboundary

/--
[rlc_jointBottomTraceFrontier_adj_safeTraceGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomTraceFrontier_adj_safeTraceGraph_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : rect 0 (2 * n) (-n) n}
-- given
  (hn : 0 < n)
  (hu : (u : Site 2) ∈ rlc_jointBottomTraceFrontier gamma delta)
  (hv : (v : Site 2) ∈ rlc_jointBottomTraceFrontier gamma delta)
  (he : s((u : Site 2), (v : Site 2)) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1)
  (hadj : ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)).Adj u v) :
-- imply
  (rlc_rightSafeTraceGraph gamma delta).Adj u v := by
-- proof
  apply StatMech.Universality.rlc_jointBottomTraceFrontier_adj_safeTraceGraph hn gamma delta hu hv he hadj

/--
[rlc_jointBottomTraceFrontier_walk_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_jointBottomTraceFrontier_walk_safe_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {x y : rect 0 (2 * n) (-n) n}
  {w : (rlc_rightTraceGraph gamma delta).Walk x y}
-- given
  (hn : 0 < n)
  (hfrontier : ∀ z ∈ w.support, (z : Site 2) ∈ rlc_jointBottomTraceFrontier gamma delta) :
-- imply
  (rlc_rightSafeTraceGraph gamma delta).Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_jointBottomTraceFrontier_walk_safe hn gamma delta w hfrontier

/--
[rlc_rightSafeTraceGraph_reachable_iff_traceWalk_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceGraph_reachable_iff_traceWalk_safe_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : rect 0 (2 * n) (-n) n}
-- given
  (hu : (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta) :
-- imply
  (rlc_rightSafeTraceGraph gamma delta).Reachable u v ↔ ∃ p : (rlc_rightTraceGraph gamma delta).Walk u v, ∀ z ∈ p.support, (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceGraph_reachable_iff_traceWalk_safe gamma delta hu

/--
[rlc_rightLeftTraceHeights_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightLeftTraceHeights_nonempty_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  (rlc_rightLeftTraceHeights gamma delta).Nonempty := by
-- proof
  apply StatMech.Universality.rlc_rightLeftTraceHeights_nonempty gamma delta

/--
[rlc_rightLeftTraceMin_mem_heights](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightLeftTraceMin_mem_heights_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  rlc_rightLeftTraceMin gamma delta ∈ rlc_rightLeftTraceHeights gamma delta := by
-- proof
  apply StatMech.Universality.rlc_rightLeftTraceMin_mem_heights gamma delta

/--
[rlc_rightLeftTraceMinVertex_mem_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightLeftTraceMinVertex_mem_union_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  rlc_rightLeftTraceMinVertex gamma delta ∈ rlc_pathVertices gamma.1 ∪ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_rightLeftTraceMinVertex_mem_union gamma delta

/--
[rlc_rightLeftTraceMinVertex_lowerHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightLeftTraceMinVertex_lowerHalf_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  rlc_rightLeftTraceMinVertex gamma delta ∈ rlc_lowerHalf := by
-- proof
  apply StatMech.Universality.rlc_rightLeftTraceMinVertex_lowerHalf gamma delta

/--
[rlc_rightLeftTraceMinVertex_mem_strictBelow_of_not_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightLeftTraceMinVertex_mem_strictBelow_of_not_path_eq
  {n : ℤ}
  {gamma delta eta : RlcRightDiagonalPath n}
-- given
  (heta : eta = gamma ∨ eta = delta)
  (hnot : rlc_rightLeftTraceMinVertex gamma delta ∉ rlc_pathVertices eta.1) :
-- imply
  rlc_rightLeftTraceMinVertex gamma delta ∈ rlc_strictBelowSet eta := by
-- proof
  apply StatMech.Universality.rlc_rightLeftTraceMinVertex_mem_strictBelow_of_not_path gamma delta eta heta hnot

/--
[rlc_rightLeftTraceMinVertex_not_upperUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightLeftTraceMinVertex_not_upperUnion_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  rlc_rightLeftTraceMinVertex gamma delta ∉ rlc_rightUpperUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_rightLeftTraceMinVertex_not_upperUnion hn gamma delta

/--
[rlc_exists_safe_left_trace_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_exists_safe_left_trace_anchor_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  ∃ x : leftSide 0 (2 * n) (-n) n, (x : Site 2) ∈ rlc_lowerHalf ∧ (x : Site 2) ∈ rlc_pathVertices gamma.1 ∪ rlc_pathVertices delta.1 ∧ (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_exists_safe_left_trace_anchor hn gamma delta

/--
[rlc_rightLeftTraceMinSide_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightLeftTraceMinSide_val_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  (rlc_rightLeftTraceMinSide gamma delta : Site 2) = rlc_rightLeftTraceMinVertex gamma delta := by
-- proof
  apply StatMech.Universality.rlc_rightLeftTraceMinSide_val gamma delta

/--
[rlc_rightLeftTraceMinVertex_mem_jointBottomTraceFrontier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightLeftTraceMinVertex_mem_jointBottomTraceFrontier_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n} :
-- imply
  rlc_rightLeftTraceMinVertex gamma delta ∈ rlc_jointBottomTraceFrontier gamma delta := by
-- proof
  apply StatMech.Universality.rlc_rightLeftTraceMinVertex_mem_jointBottomTraceFrontier gamma delta

/--
[rlc_commonRightPathVertex_not_upperUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_commonRightPathVertex_not_upperUnion_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {z : Site 2}
-- given
  (hzGamma : z ∈ rlc_pathVertices gamma.1)
  (hzDelta : z ∈ rlc_pathVertices delta.1) :
-- imply
  z ∉ rlc_rightUpperUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_commonRightPathVertex_not_upperUnion gamma delta hzGamma hzDelta

/--
[rlc_walk_pred_first_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_walk_pred_first_exit_eq
  {G : SimpleGraph V}
  {x y : V}
  {w : G.Walk x y}
-- given
  (P : V → Prop)
  (hx : P x)
  (hy : ¬ P y) :
-- imply
  ∃ u v, s(u, v) ∈ w.edges ∧ P u ∧ ¬ P v := by
-- proof
  apply StatMech.Universality.rlc_walk_pred_first_exit w P hx hy

/--
[rlc_walk_pred_first_exit_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_walk_pred_first_exit_prefix_eq
  {G : SimpleGraph V}
  {x y : V}
  {w : G.Walk x y}
-- given
  (P : V → Prop)
  (hx : P x)
  (hy : ¬ P y) :
-- imply
  ∃ (u v : V) (q : G.Walk x u), G.Adj u v ∧ s(u, v) ∈ w.edges ∧ (∀ e ∈ q.edges, e ∈ w.edges) ∧ (∀ z ∈ q.support, P z) ∧ ¬ P v := by
-- proof
  apply StatMech.Universality.rlc_walk_pred_first_exit_prefix w P hx hy

/--
[rlc_rightTrace_switchPoint_of_enter_upperUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightTrace_switchPoint_of_enter_upperUnion_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (he : s(u, v) ∈ rlc_pathEdges gamma.1)
  (hu : u ∉ rlc_rightUpperUnionSet gamma delta)
  (hv : v ∈ rlc_rightUpperUnionSet gamma delta) :
-- imply
  u ∈ rlc_pathVertices gamma.1 ∧ u ∈ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_rightTrace_switchPoint_of_enter_upperUnion gamma delta he hu hv

/--
[rlc_rightTrace_switchPoint_of_enter_upperUnion'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightTrace_switchPoint_of_enter_upperUnion'_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : Site 2}
-- given
  (he : s(u, v) ∈ rlc_pathEdges delta.1)
  (hu : u ∉ rlc_rightUpperUnionSet gamma delta)
  (hv : v ∈ rlc_rightUpperUnionSet gamma delta) :
-- imply
  u ∈ rlc_pathVertices gamma.1 ∧ u ∈ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_rightTrace_switchPoint_of_enter_upperUnion' gamma delta he hu hv

/--
[rlc_rightTrace_common_switch_before_unsafe_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightTrace_common_switch_before_unsafe_end_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hstart : (gamma.1.1 : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
  (hend : (gamma.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta) :
-- imply
  ∃ u v : rect 0 (2 * n) (-n) n, s((u : Site 2), (v : Site 2)) ∈ rlc_pathEdges gamma.1 ∧ (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (v : Site 2) ∈ rlc_rightUpperUnionSet gamma delta ∧ (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧ (u : Site 2) ∈ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_rightTrace_common_switch_before_unsafe_end gamma delta hstart hend

/--
[rlc_rightTrace_common_switch_before_unsafe_end'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightTrace_common_switch_before_unsafe_end'_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hstart : (delta.1.1 : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
  (hend : (delta.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta) :
-- imply
  ∃ u v : rect 0 (2 * n) (-n) n, s((u : Site 2), (v : Site 2)) ∈ rlc_pathEdges delta.1 ∧ (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (v : Site 2) ∈ rlc_rightUpperUnionSet gamma delta ∧ (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧ (u : Site 2) ∈ rlc_pathVertices delta.1 := by
-- proof
  apply StatMech.Universality.rlc_rightTrace_common_switch_before_unsafe_end' gamma delta hstart hend

/--
[rlc_rightSafeTrace_reaches_common_before_unsafe_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTrace_reaches_common_before_unsafe_end_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hstart : (gamma.1.1 : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
  (hend : (gamma.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta) :
-- imply
  ∃ u : rect 0 (2 * n) (-n) n, (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧ (u : Site 2) ∈ rlc_pathVertices delta.1 ∧ (rlc_rightSafeTraceGraph gamma delta).Reachable ⟨gamma.1.1, leftSide_subset gamma.1.1.2⟩ u := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTrace_reaches_common_before_unsafe_end gamma delta hstart hend

/--
[rlc_rightSafeTrace_reaches_common_from_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTrace_reaches_common_from_vertex_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {z : rect 0 (2 * n) (-n) n}
-- given
  (hz : z ∈ gamma.1.2.2.1.support)
  (hzSafe : (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
  (hend : (gamma.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta) :
-- imply
  ∃ u : rect 0 (2 * n) (-n) n, (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧ (u : Site 2) ∈ rlc_pathVertices delta.1 ∧ (rlc_rightSafeTraceGraph gamma delta).Reachable z u := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTrace_reaches_common_from_vertex gamma delta hz hzSafe hend

/--
[rlc_safe_vertex_reaches_endpoint_or_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_safe_vertex_reaches_endpoint_or_common_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {z : rect 0 (2 * n) (-n) n}
-- given
  (hz : z ∈ gamma.1.2.2.1.support)
  (hzSafe : (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta) :
-- imply
  (rlc_rightSafeTraceGraph gamma delta).Reachable z ⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ ∨ ∃ u : rect 0 (2 * n) (-n) n, (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧ (u : Site 2) ∈ rlc_pathVertices delta.1 ∧ (rlc_rightSafeTraceGraph gamma delta).Reachable z u := by
-- proof
  apply StatMech.Universality.rlc_safe_vertex_reaches_endpoint_or_common gamma delta hz hzSafe

/--
[rlc_safe_left_anchor_reaches_common_of_unsafe_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_safe_left_anchor_reaches_common_of_unsafe_ends_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n)
  (hgammaEnd : (gamma.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta)
  (hdeltaEnd : (delta.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta) :
-- imply
  ∃ (z : leftSide 0 (2 * n) (-n) n) (u : rect 0 (2 * n) (-n) n), (z : Site 2) ∈ rlc_lowerHalf ∧ (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧ (u : Site 2) ∈ rlc_pathVertices delta.1 ∧ (rlc_rightSafeTraceGraph gamma delta).Reachable ⟨z, leftSide_subset z.2⟩ u := by
-- proof
  apply StatMech.Universality.rlc_safe_left_anchor_reaches_common_of_unsafe_ends hn gamma delta hgammaEnd hdeltaEnd

/--
[rlc_rightSafeTraceGraph_adj_of_pathEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceGraph_adj_of_pathEdge_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : rect 0 (2 * n) (-n) n}
-- given
  (he : s((u : Site 2), (v : Site 2)) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1)
  (hu : (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
  (hv : (v : Site 2) ∉ rlc_rightUpperUnionSet gamma delta) :
-- imply
  (rlc_rightSafeTraceGraph gamma delta).Adj u v := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceGraph_adj_of_pathEdge gamma delta he hu hv

/--
[rlc_rightSafeTraceGraph_reachable_dest_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceGraph_reachable_dest_safe_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {u v : rect 0 (2 * n) (-n) n}
-- given
  (hu : (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
  (hreach : (rlc_rightSafeTraceGraph gamma delta).Reachable u v) :
-- imply
  (v : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceGraph_reachable_dest_safe gamma delta hu hreach

/--
[rlc_rightSafeTraceReachable_of_path_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceReachable_of_path_safe_eq
  {n : ℤ}
  {gamma delta eta : RlcRightDiagonalPath n}
-- given
  (hedges : rlc_pathEdges eta.1 ⊆ rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1)
  (hsafe : Disjoint (rlc_rightUpperUnionSet gamma delta) (rlc_pathVertices eta.1 : Set (Site 2))) :
-- imply
  ∃ (x : leftSide 0 (2 * n) (-n) n) (y : rightSide 0 (2 * n) (-n) n), (x : Site 2) ∈ rlc_lowerHalf ∧ (y : Site 2) ∈ rlc_upperHalf ∧ (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (rlc_rightSafeTraceGraph gamma delta).Reachable ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceReachable_of_path_safe gamma delta eta hedges hsafe

/--
[rlc_rightSafeTraceReachable_of_left_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceReachable_of_left_trace_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hcross : Disjoint (rlc_strictTopSet delta) (rlc_pathVertices gamma.1 : Set (Site 2))) :
-- imply
  ∃ (x : leftSide 0 (2 * n) (-n) n) (y : rightSide 0 (2 * n) (-n) n), (x : Site 2) ∈ rlc_lowerHalf ∧ (y : Site 2) ∈ rlc_upperHalf ∧ (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (rlc_rightSafeTraceGraph gamma delta).Reachable ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceReachable_of_left_trace gamma delta hcross

/--
[rlc_rightSafeTraceReachable_of_right_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceReachable_of_right_trace_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hcross : Disjoint (rlc_strictTopSet gamma) (rlc_pathVertices delta.1 : Set (Site 2))) :
-- imply
  ∃ (x : leftSide 0 (2 * n) (-n) n) (y : rightSide 0 (2 * n) (-n) n), (x : Site 2) ∈ rlc_lowerHalf ∧ (y : Site 2) ∈ rlc_upperHalf ∧ (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (rlc_rightSafeTraceGraph gamma delta).Reachable ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceReachable_of_right_trace gamma delta hcross

/--
[rlc_rightSafeTraceReachable_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceReachable_self_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  ∃ (x : leftSide 0 (2 * n) (-n) n) (y : rightSide 0 (2 * n) (-n) n), (x : Site 2) ∈ rlc_lowerHalf ∧ (y : Site 2) ∈ rlc_upperHalf ∧ (x : Site 2) ∉ rlc_rightUpperUnionSet gamma gamma ∧ (y : Site 2) ∉ rlc_rightUpperUnionSet gamma gamma ∧ (rlc_rightSafeTraceGraph gamma gamma).Reachable ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceReachable_self gamma

/--
[rlc_rightSafeTraceReachable_of_disjoint_start_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceReachable_of_disjoint_start_left_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hdisj : Disjoint (rlc_pathVertices delta.1) (rlc_pathVertices gamma.1))
  (hstart : (gamma.1.1 : Site 2) ∉ rlc_strictTopSet delta) :
-- imply
  ∃ (x : leftSide 0 (2 * n) (-n) n) (y : rightSide 0 (2 * n) (-n) n), (x : Site 2) ∈ rlc_lowerHalf ∧ (y : Site 2) ∈ rlc_upperHalf ∧ (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (rlc_rightSafeTraceGraph gamma delta).Reachable ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceReachable_of_disjoint_start_left gamma delta hdisj hstart

/--
[rlc_rightSafeTraceReachable_of_disjoint_start_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceReachable_of_disjoint_start_right_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1))
  (hstart : (delta.1.1 : Site 2) ∉ rlc_strictTopSet gamma) :
-- imply
  ∃ (x : leftSide 0 (2 * n) (-n) n) (y : rightSide 0 (2 * n) (-n) n), (x : Site 2) ∈ rlc_lowerHalf ∧ (y : Site 2) ∈ rlc_upperHalf ∧ (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (rlc_rightSafeTraceGraph gamma delta).Reachable ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceReachable_of_disjoint_start_right gamma delta hdisj hstart

/--
[rlc_rightSafeTraceReachable_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceReachable_of_disjoint_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n)
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1)) :
-- imply
  ∃ (x : leftSide 0 (2 * n) (-n) n) (y : rightSide 0 (2 * n) (-n) n), (x : Site 2) ∈ rlc_lowerHalf ∧ (y : Site 2) ∈ rlc_upperHalf ∧ (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧ (rlc_rightSafeTraceGraph gamma delta).Reachable ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceReachable_of_disjoint hn gamma delta hdisj

/--
[rlc_rightCommonSupport_nonempty_of_not_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightCommonSupport_nonempty_of_not_disjoint_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hinter : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1)) :
-- imply
  (rlc_rightCommonSupport gamma delta).Nonempty := by
-- proof
  apply StatMech.Universality.rlc_rightCommonSupport_nonempty_of_not_disjoint gamma delta hinter

/--
[rlc_exists_min_rightCommonSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_exists_min_rightCommonSupport_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hinter : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1)) :
-- imply
  ∃ z : ↑(rlc_rightCommonSupport gamma delta), ∀ q : ↑(rlc_rightCommonSupport gamma delta), rlc_rightCommonRank gamma delta z ≤ rlc_rightCommonRank gamma delta q := by
-- proof
  apply StatMech.Universality.rlc_exists_min_rightCommonSupport gamma delta hinter

/--
[rlc_min_rightCommon_prefixes_inter_only](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_min_rightCommon_prefixes_inter_only_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {z : ↑(rlc_rightCommonSupport gamma delta)}
  {q : rect 0 (2 * n) (-n) n}
-- given
  (hzGamma : z.1 ∈ gamma.1.2.2.1.support)
  (hzDelta : z.1 ∈ delta.1.2.2.1.support)
  (hmin : ∀ q : ↑(rlc_rightCommonSupport gamma delta), rlc_rightCommonRank gamma delta z ≤ rlc_rightCommonRank gamma delta q)
  (hqGamma : q ∈ (gamma.1.2.2.1.takeUntil z.1 hzGamma).support)
  (hqDelta : q ∈ (delta.1.2.2.1.takeUntil z.1 hzDelta).support) :
-- imply
  q = z.1 := by
-- proof
  apply StatMech.Universality.rlc_min_rightCommon_prefixes_inter_only gamma delta z hzGamma hzDelta hmin hqGamma hqDelta

/--
[rlc_exists_min_gamma_reverse_rightCommonSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_exists_min_gamma_reverse_rightCommonSupport_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hinter : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1)) :
-- imply
  ∃ z : ↑(rlc_rightCommonSupport gamma delta), ∀ q : ↑(rlc_rightCommonSupport gamma delta), rlc_rightCommonGammaReverseRank gamma delta z ≤ rlc_rightCommonGammaReverseRank gamma delta q := by
-- proof
  apply StatMech.Universality.rlc_exists_min_gamma_reverse_rightCommonSupport gamma delta hinter

/--
[rlc_min_gamma_reverse_rightCommon_prefix_inter_only](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_min_gamma_reverse_rightCommon_prefix_inter_only_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {z : ↑(rlc_rightCommonSupport gamma delta)}
  {q : rect 0 (2 * n) (-n) n}
-- given
  (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support)
  (hmin : ∀ q : ↑(rlc_rightCommonSupport gamma delta), rlc_rightCommonGammaReverseRank gamma delta z ≤ rlc_rightCommonGammaReverseRank gamma delta q)
  (hqGamma : q ∈ (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).support)
  (hqDelta : q ∈ delta.1.2.2.1.support) :
-- imply
  q = z.1 := by
-- proof
  apply StatMech.Universality.rlc_min_gamma_reverse_rightCommon_prefix_inter_only gamma delta z hzGamma hmin hqGamma hqDelta

/--
[rlc_last_gamma_terminal_suffix_top_of_unsafe_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_last_gamma_terminal_suffix_top_of_unsafe_end_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hinter : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1))
  (hgammaEnd : (gamma.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta) :
-- imply
  ∃ (z : ↑(rlc_rightCommonSupport gamma delta)) (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support), let pg := gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma ¬ pg.Nil ∧ (∀ q ∈ pg.dropLast.support, (q : Site 2) ∉ rlc_pathVertices delta.1) ∧ (∀ q ∈ pg.dropLast.support, (q : Site 2) ∈ rlc_strictTopSet delta) := by
-- proof
  apply StatMech.Universality.rlc_last_gamma_terminal_suffix_top_of_unsafe_end gamma delta hinter hgammaEnd

/--
[rlc_last_delta_terminal_suffix_top_of_unsafe_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_last_delta_terminal_suffix_top_of_unsafe_end_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hinter : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1))
  (hdeltaEnd : (delta.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta) :
-- imply
  ∃ (z : ↑(rlc_rightCommonSupport delta gamma)) (hzDelta : z.1 ∈ delta.1.2.2.1.reverse.support), let pd := delta.1.2.2.1.reverse.takeUntil z.1 hzDelta ¬ pd.Nil ∧ (∀ q ∈ pd.dropLast.support, (q : Site 2) ∉ rlc_pathVertices gamma.1) ∧ (∀ q ∈ pd.dropLast.support, (q : Site 2) ∈ rlc_strictTopSet gamma) := by
-- proof
  apply StatMech.Universality.rlc_last_delta_terminal_suffix_top_of_unsafe_end gamma delta hinter hdeltaEnd

/--
[rlc_last_common_reaches_safe_gamma_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_last_common_reaches_safe_gamma_endpoint_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hinter : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1))
  (hgammaEnd : (gamma.1.2.1 : Site 2) ∉ rlc_rightUpperUnionSet gamma delta) :
-- imply
  ∃ z : ↑(rlc_rightCommonSupport gamma delta), (rlc_rightSafeTraceGraph gamma delta).Reachable z.1 ⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ := by
-- proof
  apply StatMech.Universality.rlc_last_common_reaches_safe_gamma_endpoint gamma delta hinter hgammaEnd

/--
[rlc_last_common_reaches_safe_delta_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_last_common_reaches_safe_delta_endpoint_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hinter : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1))
  (hdeltaEnd : (delta.1.2.1 : Site 2) ∉ rlc_rightUpperUnionSet gamma delta) :
-- imply
  ∃ z : ↑(rlc_rightCommonSupport delta gamma), (rlc_rightSafeTraceGraph gamma delta).Reachable z.1 ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ := by
-- proof
  apply StatMech.Universality.rlc_last_common_reaches_safe_delta_endpoint gamma delta hinter hdeltaEnd

/--
[rlc_rightSafeTraceReachability_of_commonSafeConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceReachability_of_commonSafeConnectivity_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hcommon : RlcRightCommonSafeConnectivity n) :
-- imply
  RlcRightSafeTraceReachability n := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceReachability_of_commonSafeConnectivity hn hcommon

/--
[rlc_rightSafeTraceReachability_of_canonicalAnchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceReachability_of_canonicalAnchor_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hanchor : RlcRightCanonicalAnchorReachability n) :
-- imply
  RlcRightSafeTraceReachability n := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceReachability_of_canonicalAnchor hn hanchor

/--
[rlc_exists_min_reverse_rightCommonSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_exists_min_reverse_rightCommonSupport_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hinter : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1)) :
-- imply
  ∃ z : ↑(rlc_rightCommonSupport gamma delta), ∀ q : ↑(rlc_rightCommonSupport gamma delta), rlc_rightCommonReverseRank gamma delta z ≤ rlc_rightCommonReverseRank gamma delta q := by
-- proof
  apply StatMech.Universality.rlc_exists_min_reverse_rightCommonSupport gamma delta hinter

/--
[rlc_min_reverse_rightCommon_prefixes_inter_only](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_min_reverse_rightCommon_prefixes_inter_only_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {z : ↑(rlc_rightCommonSupport gamma delta)}
  {q : rect 0 (2 * n) (-n) n}
-- given
  (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support)
  (hzDelta : z.1 ∈ delta.1.2.2.1.reverse.support)
  (hmin : ∀ q : ↑(rlc_rightCommonSupport gamma delta), rlc_rightCommonReverseRank gamma delta z ≤ rlc_rightCommonReverseRank gamma delta q)
  (hqGamma : q ∈ (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).support)
  (hqDelta : q ∈ (delta.1.2.2.1.reverse.takeUntil z.1 hzDelta).support) :
-- imply
  q = z.1 := by
-- proof
  apply StatMech.Universality.rlc_min_reverse_rightCommon_prefixes_inter_only gamma delta z hzGamma hzDelta hmin hqGamma hqDelta

/--
[rlc_terminal_lens_of_unsafe_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_terminal_lens_of_unsafe_ends_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hinter : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1))
  (hgammaEnd : (gamma.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta)
  (hdeltaEnd : (delta.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta) :
-- imply
  ∃ z : ↑(rlc_rightCommonSupport gamma delta), ∃ (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support) (hzDelta : z.1 ∈ delta.1.2.2.1.reverse.support), (z.1 : Site 2) ≠ (gamma.1.2.1 : Site 2) ∧ (z.1 : Site 2) ≠ (delta.1.2.1 : Site 2) ∧ ∀ q : rect 0 (2 * n) (-n) n, q ∈ (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).support → q ∈ (delta.1.2.2.1.reverse.takeUntil z.1 hzDelta).support → q = z.1 := by
-- proof
  apply StatMech.Universality.rlc_terminal_lens_of_unsafe_ends gamma delta hinter hgammaEnd hdeltaEnd

/--
[rlc_lens_penultimate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_lens_penultimate_ne_eq
  {G : SimpleGraph V}
  {a b z : V}
  {p : G.Walk a z}
  {q : G.Walk b z}
-- given
  (ha : a ≠ z)
  (hb : b ≠ z)
  (hinter : ∀ u : V, u ∈ p.support → u ∈ q.support → u = z) :
-- imply
  p.penultimate ≠ q.penultimate := by
-- proof
  apply StatMech.Universality.rlc_lens_penultimate_ne p q ha hb hinter

/--
[rlc_terminal_lens_distinct_branches_of_unsafe_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_terminal_lens_distinct_branches_of_unsafe_ends_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hinter : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1))
  (hgammaEnd : (gamma.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta)
  (hdeltaEnd : (delta.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta) :
-- imply
  ∃ (z : ↑(rlc_rightCommonSupport gamma delta)) (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support) (hzDelta : z.1 ∈ delta.1.2.2.1.reverse.support), let pg := gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma let pd := delta.1.2.2.1.reverse.takeUntil z.1 hzDelta ¬ pg.Nil ∧ ¬ pd.Nil ∧ ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)).Adj pg.penultimate z.1 ∧ ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)).Adj pd.penultimate z.1 ∧ pg.penultimate ≠ pd.penultimate := by
-- proof
  apply StatMech.Universality.rlc_terminal_lens_distinct_branches_of_unsafe_ends gamma delta hinter hgammaEnd hdeltaEnd

/--
[rlc_rightSafeTraceReachability_of_intersecting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceReachability_of_intersecting_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hinter : RlcRightIntersectingSafeTraceReachability n) :
-- imply
  RlcRightSafeTraceReachability n := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceReachability_of_intersecting hn hinter

/--
[rlc_rightSafeTraceGraph_walk_support_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceGraph_walk_support_safe_eq
  {n : ℤ}
  {gamma delta : RlcRightDiagonalPath n}
  {x y : rect 0 (2 * n) (-n) n}
  {w : (rlc_rightSafeTraceGraph gamma delta).Walk x y}
  {z : rect 0 (2 * n) (-n) n}
-- given
  (hx : (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
  (hz : z ∈ w.support) :
-- imply
  (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceGraph_walk_support_safe gamma delta w hx hz

/--
[rlc_leftSafeTraceGraph_walk_support_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftSafeTraceGraph_walk_support_safe_eq
  {n : ℤ}
  {gamma delta : RlcLeftDiagonalPath n}
  {x y : rect (-2 * n) 0 (-n) n}
  {w : (rlc_leftSafeTraceGraph gamma delta).Walk x y}
  {z : rect (-2 * n) 0 (-n) n}
-- given
  (hx : (x : Site 2) ∉ rlc_leftLowerUnionSet gamma delta)
  (hz : z ∈ w.support) :
-- imply
  (z : Site 2) ∉ rlc_leftLowerUnionSet gamma delta := by
-- proof
  apply StatMech.Universality.rlc_leftSafeTraceGraph_walk_support_safe gamma delta w hx hz

/--
[rlc_rightSafeTraceReachability_of_frontierPathProperty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceReachability_of_frontierPathProperty_eq
  {n : ℤ}
-- given
  (hfrontier : RlcRightFrontierPathProperty n) :
-- imply
  RlcRightSafeTraceReachability n := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceReachability_of_frontierPathProperty hfrontier

/--
[rlc_rightFrontierPathProperty_of_safeTraceReachability](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightFrontierPathProperty_of_safeTraceReachability_eq
  {n : ℤ}
-- given
  (hsafe : RlcRightSafeTraceReachability n) :
-- imply
  RlcRightFrontierPathProperty n := by
-- proof
  apply StatMech.Universality.rlc_rightFrontierPathProperty_of_safeTraceReachability hsafe

/--
[rlc_rightSafeTraceReachability_iff_frontierPathProperty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightSafeTraceReachability_iff_frontierPathProperty_eq
  {n : ℤ} :
-- imply
  RlcRightSafeTraceReachability n ↔ RlcRightFrontierPathProperty n := by
-- proof
  apply StatMech.Universality.rlc_rightSafeTraceReachability_iff_frontierPathProperty

/--
[rlc_leftFrontierPathProperty_of_safeTraceReachability](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftFrontierPathProperty_of_safeTraceReachability_eq
  {n : ℤ}
-- given
  (hsafe : RlcLeftSafeTraceReachability n) :
-- imply
  RlcLeftFrontierPathProperty n := by
-- proof
  apply StatMech.Universality.rlc_leftFrontierPathProperty_of_safeTraceReachability hsafe

/--
[rlc_leftFrontierPathProperty_of_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftFrontierPathProperty_of_right_eq
  {n : ℤ}
-- given
  (hright : RlcRightFrontierPathProperty n) :
-- imply
  RlcLeftFrontierPathProperty n := by
-- proof
  apply StatMech.Universality.rlc_leftFrontierPathProperty_of_right hright

/--
[rlc_rightEnvelopeProperty_of_frontierPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightEnvelopeProperty_of_frontierPath_eq
  {n : ℤ}
-- given
  (hfrontier : RlcRightFrontierPathProperty n) :
-- imply
  RlcRightEnvelopeProperty n := by
-- proof
  apply StatMech.Universality.rlc_rightEnvelopeProperty_of_frontierPath hfrontier

/--
[rlc_leftEnvelopeProperty_of_frontierPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftEnvelopeProperty_of_frontierPath_eq
  {n : ℤ}
-- given
  (hfrontier : RlcLeftFrontierPathProperty n) :
-- imply
  RlcLeftEnvelopeProperty n := by
-- proof
  apply StatMech.Universality.rlc_leftEnvelopeProperty_of_frontierPath hfrontier

/--
[rlc_envelopeProperties_of_rightSafeTraceReachability](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_envelopeProperties_of_rightSafeTraceReachability_eq
  {n : ℤ}
-- given
  (hsafe : RlcRightSafeTraceReachability n) :
-- imply
  RlcRightEnvelopeProperty n ∧ RlcLeftEnvelopeProperty n := by
-- proof
  apply StatMech.Universality.rlc_envelopeProperties_of_rightSafeTraceReachability hsafe

/--
[rlc_pathOpen_of_edges_subset_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathOpen_of_edges_subset_union_eq
  {a b c d : ℤ}
  {lambda gamma delta : RlcCrossingPath a b c d}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hedges : rlc_pathEdges lambda ⊆ rlc_pathEdges gamma ∪ rlc_pathEdges delta)
  (hgamma : omega ∈ rlc_pathOpen gamma)
  (hdelta : omega ∈ rlc_pathOpen delta) :
-- imply
  omega ∈ rlc_pathOpen lambda := by
-- proof
  apply StatMech.Universality.rlc_pathOpen_of_edges_subset_union lambda gamma delta hedges hgamma hdelta

/--
[rlc_rightLowestCandidate_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightLowestCandidate_pairwiseDisjoint_eq
  {n : ℤ}
-- given
  (henv : RlcRightEnvelopeProperty n) :
-- imply
  Pairwise (Disjoint on fun gamma : RlcRightDiagonalPath n => rlc_rightLowestCandidate gamma) := by
-- proof
  apply StatMech.Universality.rlc_rightLowestCandidate_pairwiseDisjoint henv

/--
[rlc_leftHighestCandidate_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftHighestCandidate_pairwiseDisjoint_eq
  {n : ℤ}
-- given
  (henv : RlcLeftEnvelopeProperty n) :
-- imply
  Pairwise (Disjoint on fun gamma : RlcLeftDiagonalPath n => rlc_leftHighestCandidate gamma) := by
-- proof
  apply StatMech.Universality.rlc_leftHighestCandidate_pairwiseDisjoint henv

/--
[rlc_extremalPairCandidate_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_extremalPairCandidate_pairwiseDisjoint_eq
  {n : ℤ}
-- given
  (hright : RlcRightEnvelopeProperty n)
  (hleft : RlcLeftEnvelopeProperty n) :
-- imply
  Pairwise (Disjoint on fun pair : RlcDiagonalPathPair n => rlc_extremalPairCandidate pair) := by
-- proof
  apply StatMech.Universality.rlc_extremalPairCandidate_pairwiseDisjoint hright hleft

/--
[rlc_flipX_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipX_involutive_eq
  {x : Site 2} :
-- imply
  rlc_flipX (rlc_flipX x) = x := by
-- proof
  apply StatMech.Universality.rlc_flipX_involutive x

/--
[rlc_flipX_eq_self_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_flipX_eq_self_of_zero_eq
  {x : Site 2}
-- given
  (hx : x 0 = 0) :
-- imply
  rlc_flipX x = x := by
-- proof
  apply StatMech.Universality.rlc_flipX_eq_self_of_zero hx

/--
[rlc_mem_axisHeights_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_axisHeights_iff_eq
  {P : Finset (Site 2)}
  {t : ℤ} :
-- imply
  t ∈ rlc_axisHeights P ↔ ![0, t] ∈ P := by
-- proof
  apply StatMech.Universality.rlc_mem_axisHeights_iff P t

/--
[rlc_exists_finset_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_exists_finset_gap_eq
  {A B : Finset ℤ}
  {x y : ℤ}
-- given
  (hx : x ∈ A)
  (hy : y ∈ B)
  (hxy : x < y) :
-- imply
  ∃ a b : ℤ, a ∈ A ∧ b ∈ B ∧ x ≤ a ∧ a < b ∧ b ≤ y ∧ ∀ t : ℤ, a < t → t < b → t ∉ A ∧ t ∉ B := by
-- proof
  apply StatMech.Universality.rlc_exists_finset_gap A B hx hy hxy

/--
[rlc_axis_mem_connectorBarrier_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axis_mem_connectorBarrier_iff_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {t : ℤ} :
-- imply
  ![0, t] ∈ rlc_connectorBarrier gamma gamma' ↔ ![0, t] ∈ rlc_pathVertices gamma.1 ∨ ![0, t] ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_axis_mem_connectorBarrier_iff gamma gamma' t

/--
[rlc_connectorOriginRegionSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorOriginRegionSet_finite_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  (rlc_connectorOriginRegionSet gamma gamma').Finite := by
-- proof
  apply StatMech.Universality.rlc_connectorOriginRegionSet_finite gamma gamma'

/--
[rlc_maskConfig_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_maskConfig_congr_eq
  {U : Finset (Sym2 (Site 2))}
  {omega omega' : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ e ∈ (U : Set (Sym2 (Site 2))), omega e = omega' e) :
-- imply
  rlc_maskConfig U omega = rlc_maskConfig U omega' := by
-- proof
  apply StatMech.Universality.rlc_maskConfig_congr h

/--
[rlc_maskConfig_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_maskConfig_mono_eq
  {U : Finset (Sym2 (Site 2))}
  {omega omega' : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : omega ≤ omega') :
-- imply
  rlc_maskConfig U omega ≤ rlc_maskConfig U omega' := by
-- proof
  apply StatMech.Universality.rlc_maskConfig_mono U h

/--
[rlc_connectorEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorEvent_dependsOn_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  DependsOn ((rlc_connectorEvent gamma gamma').indicator (fun _ => (1 : ℝ))) (rlc_connectorEdges gamma gamma' : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_connectorEvent_dependsOn gamma gamma'

/--
[rlc_connectorEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorEvent_measurableSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  MeasurableSet (rlc_connectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorEvent_measurableSet gamma gamma'

/--
[rlc_maskConfig_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_maskConfig_le_eq
  {U : Finset (Sym2 (Site 2))}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  rlc_maskConfig U omega ≤ omega := by
-- proof
  apply StatMech.Universality.rlc_maskConfig_le U omega

/--
[rlc_pathOpen_connected_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathOpen_connected_start_eq
  {a b c d : ℤ}
  {gamma : RlcCrossingPath a b c d}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {z : Site 2}
-- given
  (hopen : omega ∈ rlc_pathOpen gamma)
  (hz : z ∈ rlc_pathVertices gamma) :
-- imply
  ∃ hzR : z ∈ rect a b c d, ConnectedWithin 2 omega (rect a b c d) ⟨(gamma.1 : Site 2), leftSide_subset gamma.1.2⟩ ⟨z, hzR⟩ := by
-- proof
  apply StatMech.Universality.rlc_pathOpen_connected_start gamma omega hopen hz

/--
[rlc_pathOpen_connected_finish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathOpen_connected_finish_eq
  {a b c d : ℤ}
  {gamma : RlcCrossingPath a b c d}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {z : Site 2}
-- given
  (hopen : omega ∈ rlc_pathOpen gamma)
  (hz : z ∈ rlc_pathVertices gamma) :
-- imply
  ∃ hzR : z ∈ rect a b c d, ConnectedWithin 2 omega (rect a b c d) ⟨z, hzR⟩ ⟨(gamma.2.1 : Site 2), rightSide_subset gamma.2.1.2⟩ := by
-- proof
  apply StatMech.Universality.rlc_pathOpen_connected_finish gamma omega hopen hz

/--
[rlc_connector_glues_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connector_glues_horizontal_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (_hn : 0 < n) :
-- imply
  rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩ rlc_connectorEvent gamma gamma' ⊆ horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_connector_glues_horizontal n _hn gamma gamma'

/--
[rlc_originRegion_not_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_originRegion_not_barrier_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_connectorOriginRegion gamma gamma') :
-- imply
  z ∉ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_originRegion_not_barrier hz

/--
[rlc_rightPathEdges_disjoint_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathEdges_disjoint_connector_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Disjoint (rlc_pathEdges gamma.1) (rlc_connectorEdges gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_rightPathEdges_disjoint_connector gamma gamma'

/--
[rlc_leftPathEdges_disjoint_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathEdges_disjoint_connector_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Disjoint (rlc_pathEdges gamma'.1) (rlc_connectorEdges gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_leftPathEdges_disjoint_connector gamma gamma'

/--
[rlc_rightPathVertex_mem_connectorBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathVertex_mem_connectorBox_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_pathVertices gamma.1) :
-- imply
  z ∈ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_rightPathVertex_mem_connectorBox gamma hz

/--
[rlc_leftPathVertex_mem_connectorBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathVertex_mem_connectorBox_eq
  {n : ℤ}
  {gamma : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_pathVertices gamma.1) :
-- imply
  z ∈ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_leftPathVertex_mem_connectorBox gamma hz

/--
[rlc_mem_connectorEvent_of_common_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_connectorEvent_of_common_vertex_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_pathVertices gamma.1)
  (hz' : z ∈ rlc_pathVertices gamma'.1) :
-- imply
  omega ∈ rlc_connectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_mem_connectorEvent_of_common_vertex gamma gamma' omega hz hz'

/--
[rlc_pathVertices_disjoint_of_not_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pathVertices_disjoint_of_not_connector_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_connectorEvent gamma gamma') :
-- imply
  Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1) := by
-- proof
  apply StatMech.Universality.rlc_pathVertices_disjoint_of_not_connector gamma gamma' omega hno

/--
[rlc_axis_endpoints_strict_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axis_endpoints_strict_of_disjoint_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  (gamma.1.1 : Site 2) 1 < (gamma'.1.2.1 : Site 2) 1 := by
-- proof
  apply StatMech.Universality.rlc_axis_endpoints_strict_of_disjoint gamma gamma' hdisj

/--
[rlc_axis_endpoints_strict_of_not_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axis_endpoints_strict_of_not_connector_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_connectorEvent gamma gamma') :
-- imply
  (gamma.1.1 : Site 2) 1 < (gamma'.1.2.1 : Site 2) 1 := by
-- proof
  apply StatMech.Universality.rlc_axis_endpoints_strict_of_not_connector gamma gamma' omega hno

/--
[rlc_exists_axis_barrier_gap_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_exists_axis_barrier_gap_of_disjoint_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  ∃ a b : ℤ, a ∈ rlc_axisHeights (rlc_pathVertices gamma.1) ∧ b ∈ rlc_axisHeights (rlc_pathVertices gamma'.1) ∧ (gamma.1.1 : Site 2) 1 ≤ a ∧ a < b ∧ b ≤ (gamma'.1.2.1 : Site 2) 1 ∧ ∀ t : ℤ, a < t → t < b → ![0, t] ∉ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_exists_axis_barrier_gap_of_disjoint gamma gamma' hdisj

/--
[rlc_axisBarrierGap_nonempty_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisBarrierGap_nonempty_of_disjoint_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  Nonempty (RlcAxisBarrierGap gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_axisBarrierGap_nonempty_of_disjoint gamma gamma' hdisj

/--
[rlc_axisBarrierGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisBarrierGap_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  ∃ G : RlcAxisBarrierGap gamma gamma', rlc_axisBarrierGap? gamma gamma' = some G := by
-- proof
  apply StatMech.Universality.rlc_axisBarrierGap gamma gamma' hdisj

/--
[rlc_axisBarrierGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisBarrierGap_eq_2
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hdisj : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  rlc_axisBarrierGap? gamma gamma' = none := by
-- proof
  apply StatMech.Universality.rlc_axisBarrierGap gamma gamma' hdisj

/--
[RlcAxisBarrierGap.lowerVertex_mem_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma lowerVertex_mem_right_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  G.lowerVertex ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.lowerVertex_mem_right G

/--
[RlcAxisBarrierGap.upperVertex_mem_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma upperVertex_mem_left_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  G.upperVertex ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.upperVertex_mem_left G

/--
[RlcAxisBarrierGap.seedVertex_not_barrier_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma seedVertex_not_barrier_of_lt_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (h : G.lower + 1 < G.upper) :
-- imply
  G.seedVertex ∉ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.seedVertex_not_barrier_of_lt G h

/--
[RlcAxisBarrierGap.seedVertex_mem_box_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma seedVertex_mem_box_of_lt_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hn : 0 < n)
  (h : G.lower + 1 < G.upper) :
-- imply
  G.seedVertex ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.seedVertex_mem_box_of_lt G hn h

/--
[RlcAxisBarrierGap.seedVertex_mem_allowed_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma seedVertex_mem_allowed_of_lt_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hn : 0 < n)
  (h : G.lower + 1 < G.upper) :
-- imply
  G.seedVertex ∈ rlc_connectorAllowed gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.seedVertex_mem_allowed_of_lt G hn h

/--
[RlcAxisBarrierGap.firstEdge_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma firstEdge_lattice_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  G.firstEdge ∈ (hypercubicLattice 2).edgeSet := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.firstEdge_lattice G

/--
[rlc_axisGapRegionSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapRegionSet_finite_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  (rlc_axisGapRegionSet G).Finite := by
-- proof
  apply StatMech.Universality.rlc_axisGapRegionSet_finite G

/--
[RlcAxisBarrierGap.seedVertex_mem_region_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma seedVertex_mem_region_of_lt_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hn : 0 < n)
  (h : G.lower + 1 < G.upper) :
-- imply
  G.seedVertex ∈ rlc_axisGapRegion G := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.seedVertex_mem_region_of_lt G hn h

/--
[RlcAxisBarrierGap.axisVertex_mem_region_of_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma axisVertex_mem_region_of_between_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {t : ℤ}
-- given
  (hn : 0 < n)
  (hlower : G.lower < t)
  (hupper : t < G.upper) :
-- imply
  ![0, t] ∈ rlc_axisGapRegion G := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.axisVertex_mem_region_of_between G hn hlower hupper

/--
[RlcAxisBarrierGap.verticalEdge_mem_axisGapEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma verticalEdge_mem_axisGapEdges_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {t : ℤ}
-- given
  (hn : 0 < n)
  (hlower : G.lower ≤ t)
  (hupper : t < G.upper) :
-- imply
  s(![0, t], ![0, t + 1]) ∈ rlc_axisGapEdges G := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.verticalEdge_mem_axisGapEdges G hn hlower hupper

/--
[rlc_axisGapConnectorEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapConnectorEvent_dependsOn_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  DependsOn ((rlc_axisGapConnectorEvent G).indicator (fun _ => (1 : ℝ))) (rlc_axisGapEdges G : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_axisGapConnectorEvent_dependsOn G

/--
[rlc_axisGapConnectorEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapConnectorEvent_measurableSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  MeasurableSet (rlc_axisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_axisGapConnectorEvent_measurableSet G

/--
[rlc_adaptiveConnectorEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_adaptiveConnectorEvent_measurableSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  MeasurableSet (rlc_adaptiveConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_adaptiveConnectorEvent_measurableSet gamma gamma'

/--
[rlc_adaptiveConnectorEvent_eq_univ_of_not_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_adaptiveConnectorEvent_eq_univ_of_not_disjoint_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hdisj : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  rlc_adaptiveConnectorEvent gamma gamma' = Set.univ := by
-- proof
  apply StatMech.Universality.rlc_adaptiveConnectorEvent_eq_univ_of_not_disjoint gamma gamma' hdisj

/--
[rlc_adaptiveConnectorEvent_eq_gap_of_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_adaptiveConnectorEvent_eq_gap_of_some_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hG : rlc_axisBarrierGap? gamma gamma' = some G) :
-- imply
  rlc_adaptiveConnectorEvent gamma gamma' = rlc_axisGapConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_adaptiveConnectorEvent_eq_gap_of_some gamma gamma' G hG

/--
[rlc_axisGapRegion_not_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapRegion_not_barrier_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_axisGapRegion G) :
-- imply
  z ∉ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisGapRegion_not_barrier hz

/--
[RlcAxisBarrierGap.seedVertex_not_right_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma seedVertex_not_right_of_disjoint_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  G.seedVertex ∉ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.seedVertex_not_right_of_disjoint G hdisj

/--
[RlcAxisBarrierGap.firstEdge_not_mem_rightPath_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma firstEdge_not_mem_rightPath_of_disjoint_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  G.firstEdge ∉ rlc_pathEdges gamma.1 := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.firstEdge_not_mem_rightPath_of_disjoint G hdisj

/--
[RlcAxisBarrierGap.firstEdge_not_mem_leftPath_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma firstEdge_not_mem_leftPath_of_disjoint_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  G.firstEdge ∉ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.firstEdge_not_mem_leftPath_of_disjoint G hdisj

/--
[rlc_rightPathEdges_disjoint_axisGapEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathEdges_disjoint_axisGapEdges_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  Disjoint (rlc_pathEdges gamma.1) (rlc_axisGapEdges G) := by
-- proof
  apply StatMech.Universality.rlc_rightPathEdges_disjoint_axisGapEdges G hdisj

/--
[rlc_leftPathEdges_disjoint_axisGapEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathEdges_disjoint_axisGapEdges_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  Disjoint (rlc_pathEdges gamma'.1) (rlc_axisGapEdges G) := by
-- proof
  apply StatMech.Universality.rlc_leftPathEdges_disjoint_axisGapEdges G hdisj

/--
[rlc_mem_axisGapConnectorEvent_of_firstEdge_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_axisGapConnectorEvent_of_firstEdge_open_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hadjGap : G.lower + 1 = G.upper)
  (hopen : omega G.firstEdge = true) :
-- imply
  omega ∈ rlc_axisGapConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mem_axisGapConnectorEvent_of_firstEdge_open G hadjGap omega hopen

/--
[rlc_axisGapConnector_half_of_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapConnector_half_of_adjacent_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hadjGap : G.lower + 1 = G.upper) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_axisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_axisGapConnector_half_of_adjacent G hadjGap

/--
[rlc_adaptiveConnector_half_of_nonadjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_adaptiveConnector_half_of_nonadjacent_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hnonadj : ∀ G : RlcAxisBarrierGap gamma gamma', G.lower + 1 < G.upper → (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_axisGapConnectorEvent G)) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_adaptiveConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_adaptiveConnector_half_of_nonadjacent gamma gamma' hnonadj

/--
[rlc_exists_axis_barrier_gap_of_not_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_exists_axis_barrier_gap_of_not_connector_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_connectorEvent gamma gamma') :
-- imply
  ∃ a b : ℤ, a ∈ rlc_axisHeights (rlc_pathVertices gamma.1) ∧ b ∈ rlc_axisHeights (rlc_pathVertices gamma'.1) ∧ (gamma.1.1 : Site 2) 1 ≤ a ∧ a < b ∧ b ≤ (gamma'.1.2.1 : Site 2) 1 ∧ ∀ t : ℤ, a < t → t < b → ![0, t] ∉ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_exists_axis_barrier_gap_of_not_connector gamma gamma' omega hno

/--
[rlc_connectorReachSet_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_subset_box_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  rlc_connectorReachSet gamma gamma' omega ⊆ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_subset_box gamma gamma' omega

/--
[rlc_connectorReachSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_finite_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  (rlc_connectorReachSet gamma gamma' omega).Finite := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_finite gamma gamma' omega

/--
[rlc_rightPathVertex_mem_connectorReachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathVertex_mem_connectorReachSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x : Site 2}
-- given
  (hx : x ∈ rlc_pathVertices gamma.1) :
-- imply
  x ∈ rlc_connectorReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hx

/--
[rlc_connectorReachSet_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_extend_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {v w : Site 2}
-- given
  (hv : v ∈ rlc_connectorReachSet gamma gamma' omega)
  (hwR : w ∈ rect (-2 * n) (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hopen : rlc_maskConfig (rlc_connectorEdges gamma gamma') omega s(v, w) = true) :
-- imply
  w ∈ rlc_connectorReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_extend gamma gamma' omega hv hwR hadj hopen

/--
[rlc_leftPathVertex_not_mem_connectorReachSet_of_not_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathVertex_not_mem_connectorReachSet_of_not_connector_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {y : Site 2}
-- given
  (hno : omega ∉ rlc_connectorEvent gamma gamma')
  (hy : y ∈ rlc_pathVertices gamma'.1) :
-- imply
  y ∉ rlc_connectorReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_leftPathVertex_not_mem_connectorReachSet_of_not_connector gamma gamma' omega hno hy

/--
[rlc_connectorReachSet_boundary_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_boundary_closed_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {v w : Site 2}
-- given
  (hv : v ∈ rlc_connectorReachSet gamma gamma' omega)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hw : w ∉ rlc_connectorReachSet gamma gamma' omega) :
-- imply
  rlc_maskConfig (rlc_connectorEdges gamma gamma') omega s(v, w) = false := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_boundary_closed gamma gamma' omega hv hadj hw

/--
[rlc_connectorReachSet_boundary_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_boundary_dual_open_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {v w : Site 2}
-- given
  (hv : v ∈ rlc_connectorReachSet gamma gamma' omega)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hw : w ∉ rlc_connectorReachSet gamma gamma' omega) :
-- imply
  dualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega) (crossEdge s(v, w)) = true := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_boundary_dual_open gamma gamma' omega hv hadj hw

/--
[rlc_connectorReachSet_edgeBoundary_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_edgeBoundary_closed_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {v w : Site 2}
-- given
  (hvw : (v, w) ∈ edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega)) :
-- imply
  rlc_maskConfig (rlc_connectorEdges gamma gamma') omega s(v, w) = false := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_edgeBoundary_closed gamma gamma' omega hvw

/--
[rlc_connectorReachSet_edgeBoundary_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_edgeBoundary_dual_open_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {v w : Site 2}
-- given
  (hvw : (v, w) ∈ edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega)) :
-- imply
  dualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega) (crossEdge s(v, w)) = true := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_edgeBoundary_dual_open gamma gamma' omega hvw

/--
[rlc_faceBoundaryWalk_edges_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_faceBoundaryWalk_edges_dual_open_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v f g : Site 2}
  {c : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega)).Walk u v}
-- given
  (hfg : s(f, g) ∈ c.edges) :
-- imply
  dualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega) (crossEdge (sharedPrimalEdge f g)) = true := by
-- proof
  apply StatMech.Universality.rlc_faceBoundaryWalk_edges_dual_open gamma gamma' omega c hfg

/--
[rlc_faceBoundaryGraph_le_openFaceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_faceBoundaryGraph_le_openFaceDual_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega) ≤ openSubgraph 2 (fci_faceDualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)) := by
-- proof
  apply StatMech.Universality.rlc_faceBoundaryGraph_le_openFaceDual gamma gamma' omega

/--
[rlc_connectorReachSet_edgeBoundary_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_edgeBoundary_nonempty_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  (edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega)).Nonempty := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_edgeBoundary_nonempty gamma gamma' omega

/--
[rlc_connectorReachSet_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_dualCircuit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega)).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_dualCircuit gamma gamma' omega

/--
[rlc_walk_mem_edgeBoundary_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_walk_mem_edgeBoundary_edges_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ∃ u v, (u, v) ∈ edgeBoundary 2 S ∧ s(u, v) ∈ w.edges := by
-- proof
  apply StatMech.Universality.rlc_walk_mem_edgeBoundary_edges S w hx hy

/--
[rlc_connectorReachSet_axis_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_axis_boundary_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_connectorEvent gamma gamma') :
-- imply
  ∃ p q : Site 2, (p, q) ∈ edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega) ∧ p ∈ rect (-2 * n) (2 * n) (-n) n ∧ q ∈ rect (-2 * n) (2 * n) (-n) n ∧ p 0 = 0 ∧ q 0 = 0 := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_axis_boundary gamma gamma' omega hno

/--
[rlc_connectorReachSet_axis_anchored_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_axis_anchored_dualCircuit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_connectorEvent gamma gamma') :
-- imply
  ∃ (p q f g u : Site 2) (c : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega)).Walk u u), (p, q) ∈ edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega) ∧ p ∈ rect (-2 * n) (2 * n) (-n) n ∧ q ∈ rect (-2 * n) (2 * n) (-n) n ∧ p 0 = 0 ∧ q 0 = 0 ∧ (faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega)).Adj f g ∧ sharedPrimalEdge f g = s(p, q) ∧ c.IsCycle ∧ s(f, g) ∈ c.edges := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_axis_anchored_dualCircuit gamma gamma' omega hno

/--
[rlc_connectorReachSet_axis_anchored_openDualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_axis_anchored_openDualCircuit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_connectorEvent gamma gamma') :
-- imply
  ∃ (p q f g u : Site 2) (c : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega)).Walk u u), (p, q) ∈ edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega) ∧ p ∈ rect (-2 * n) (2 * n) (-n) n ∧ q ∈ rect (-2 * n) (2 * n) (-n) n ∧ p 0 = 0 ∧ q 0 = 0 ∧ (faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega)).Adj f g ∧ sharedPrimalEdge f g = s(p, q) ∧ c.IsCycle ∧ s(f, g) ∈ c.edges ∧ ∀ a b : Site 2, s(a, b) ∈ c.edges → dualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega) (crossEdge (sharedPrimalEdge a b)) = true := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_axis_anchored_openDualCircuit gamma gamma' omega hno

/--
[rlc_connectorReachSet_openFaceDualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_connectorReachSet_openFaceDualCircuit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_connectorEvent gamma gamma') :
-- imply
  ∃ (u : Site 2) (c : (openSubgraph 2 (fci_faceDualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega))).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_openFaceDualCircuit gamma gamma' omega hno

/--
[rlc_dualReflect_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_dualReflect_zero_eq
  {x : Site 2} :
-- imply
  rlc_dualReflect x 0 = -x 0 - 1 := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_zero x

/--
[rlc_dualReflect_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_dualReflect_one_eq
  {x : Site 2} :
-- imply
  rlc_dualReflect x 1 = x 1 + 1 := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_one x

/--
[rlc_dualReflect_symm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_dualReflect_symm_zero_eq
  {x : Site 2} :
-- imply
  rlc_dualReflect.symm x 0 = -x 0 - 1 := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_symm_zero x

/--
[rlc_dualReflect_symm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_dualReflect_symm_one_eq
  {x : Site 2} :
-- imply
  rlc_dualReflect.symm x 1 = x 1 - 1 := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_symm_one x

/--
[rlc_adj_dualReflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_adj_dualReflect_eq
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj x y ↔ (hypercubicLattice 2).Adj (rlc_dualReflect x) (rlc_dualReflect y) := by
-- proof
  apply StatMech.Universality.rlc_adj_dualReflect x y

/--
[rlc_dualReflectEdge_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_dualReflectEdge_symm_apply_eq
  {e : Sym2 (Site 2)} :
-- imply
  rlc_dualReflectEdge.symm e = e.map rlc_dualReflect.symm := by
-- proof
  apply StatMech.Universality.rlc_dualReflectEdge_symm_apply e

/--
[rlc_dualReflectConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_dualReflectConfig_apply_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  rlc_dualReflectConfig omega e = fci_faceDualConfig omega (e.map rlc_dualReflect.symm) := by
-- proof
  apply StatMech.Universality.rlc_dualReflectConfig_apply omega e

/--
[rlc_pimsEdgeEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pimsEdgeEquiv_apply_eq
  {e : Sym2 (Site 2)} :
-- imply
  rlc_pimsEdgeEquiv e = fci_faceEdgeEquiv (e.map rlc_dualReflect.symm) := by
-- proof
  apply StatMech.Universality.rlc_pimsEdgeEquiv_apply e

/--
[rlc_dualReflectConfig_eq_pims](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_dualReflectConfig_eq_pims_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  rlc_dualReflectConfig omega e = !(omega (rlc_pimsEdgeEquiv e)) := by
-- proof
  apply StatMech.Universality.rlc_dualReflectConfig_eq_pims omega e

/--
[rlc_pimsEdgeEquiv_reflected_mk_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pimsEdgeEquiv_reflected_mk_of_adj_eq
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) = sharedPrimalEdge f g := by
-- proof
  apply StatMech.Universality.rlc_pimsEdgeEquiv_reflected_mk_of_adj hfg

/--
[rlc_pimsEdgeEquiv_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pimsEdgeEquiv_horizontal_eq
  {a b : ℤ} :
-- imply
  rlc_pimsEdgeEquiv s(![a, b], ![a + 1, b]) = s(![-a - 1, b - 1], ![-a - 1, b]) := by
-- proof
  apply StatMech.Universality.rlc_pimsEdgeEquiv_horizontal a b

/--
[rlc_pimsEdgeEquiv_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_pimsEdgeEquiv_vertical_eq
  {a b : ℤ} :
-- imply
  rlc_pimsEdgeEquiv s(![a, b], ![a, b + 1]) = s(![-a - 1, b], ![-a, b]) := by
-- proof
  apply StatMech.Universality.rlc_pimsEdgeEquiv_vertical a b

/--
[rlc_reflectedEdge_eq_horizontal_of_shared_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_reflectedEdge_eq_horizontal_of_shared_vertical_eq
  {f g : Site 2}
  {t : ℤ}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hshared : sharedPrimalEdge f g = s(![0, t], ![0, t + 1])) :
-- imply
  s(rlc_dualReflect f, rlc_dualReflect g) = s(![-1, t + 1], ![0, t + 1]) := by
-- proof
  apply StatMech.Universality.rlc_reflectedEdge_eq_horizontal_of_shared_vertical hfg hshared

/--
[rlc_dualReflectConfig_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_dualReflectConfig_mk_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2} :
-- imply
  rlc_dualReflectConfig omega s(rlc_dualReflect x, rlc_dualReflect y) = fci_faceDualConfig omega s(x, y) := by
-- proof
  apply StatMech.Universality.rlc_dualReflectConfig_mk omega x y

/--
[rlc_dualReflectConfig_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_dualReflectConfig_measurePreserving_eq :
-- imply
  MeasurePreserving rlc_dualReflectConfig rba_selfDualMeasure rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.rlc_dualReflectConfig_measurePreserving

/--
[rlc_dualReflectOpenWalk_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_dualReflectOpenWalk_isCycle_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x : Site 2}
  {w : (openSubgraph 2 (fci_faceDualConfig omega)).Walk x x}
-- given
  (hw : w.IsCycle) :
-- imply
  (rlc_dualReflectOpenWalk omega w).IsCycle := by
-- proof
  apply StatMech.Universality.rlc_dualReflectOpenWalk_isCycle omega hw

/--
[rlc_axisGapReachSet_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapReachSet_subset_box_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  rlc_axisGapReachSet G omega ⊆ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_axisGapReachSet_subset_box G omega

/--
[rlc_axisGapReachSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapReachSet_finite_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  (rlc_axisGapReachSet G omega).Finite := by
-- proof
  apply StatMech.Universality.rlc_axisGapReachSet_finite G omega

/--
[rlc_rightPathVertex_mem_axisGapReachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathVertex_mem_axisGapReachSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x : Site 2}
-- given
  (hx : x ∈ rlc_pathVertices gamma.1) :
-- imply
  x ∈ rlc_axisGapReachSet G omega := by
-- proof
  apply StatMech.Universality.rlc_rightPathVertex_mem_axisGapReachSet G omega hx

/--
[rlc_axisGapReachSet_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapReachSet_extend_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {v w : Site 2}
-- given
  (hv : v ∈ rlc_axisGapReachSet G omega)
  (hwR : w ∈ rect (-2 * n) (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hopen : rlc_maskConfig (rlc_axisGapEdges G) omega s(v, w) = true) :
-- imply
  w ∈ rlc_axisGapReachSet G omega := by
-- proof
  apply StatMech.Universality.rlc_axisGapReachSet_extend G omega hv hwR hadj hopen

/--
[rlc_leftPathVertex_not_mem_axisGapReachSet_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathVertex_not_mem_axisGapReachSet_of_failure_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {y : Site 2}
-- given
  (hno : omega ∉ rlc_axisGapConnectorEvent G)
  (hy : y ∈ rlc_pathVertices gamma'.1) :
-- imply
  y ∉ rlc_axisGapReachSet G omega := by
-- proof
  apply StatMech.Universality.rlc_leftPathVertex_not_mem_axisGapReachSet_of_failure G omega hno hy

/--
[rlc_axisGapEdges_endpoints_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapEdges_endpoints_mem_box_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {v w : Site 2}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (he : s(v, w) ∈ rlc_axisGapEdges G) :
-- imply
  v ∈ rect (-2 * n) (2 * n) (-n) n ∧ w ∈ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_axisGapEdges_endpoints_mem_box G hn hlt he

/--
[rlc_axisGapReachSet_boundary_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapReachSet_boundary_closed_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {v w : Site 2}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hv : v ∈ rlc_axisGapReachSet G omega)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hw : w ∉ rlc_axisGapReachSet G omega) :
-- imply
  rlc_maskConfig (rlc_axisGapEdges G) omega s(v, w) = false := by
-- proof
  apply StatMech.Universality.rlc_axisGapReachSet_boundary_closed G hn hlt omega hv hadj hw

/--
[rlc_axisGapReachSet_edgeBoundary_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapReachSet_edgeBoundary_closed_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {v w : Site 2}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hvw : (v, w) ∈ edgeBoundary 2 (rlc_axisGapReachSet G omega)) :
-- imply
  rlc_maskConfig (rlc_axisGapEdges G) omega s(v, w) = false := by
-- proof
  apply StatMech.Universality.rlc_axisGapReachSet_edgeBoundary_closed G hn hlt omega hvw

/--
[rlc_axisGapFaceBoundaryGraph_le_openFaceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapFaceBoundaryGraph_le_openFaceDual_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper) :
-- imply
  faceBoundaryGraph (rlc_axisGapReachSet G omega) ≤ openSubgraph 2 (fci_faceDualConfig (rlc_maskConfig (rlc_axisGapEdges G) omega)) := by
-- proof
  apply StatMech.Universality.rlc_axisGapFaceBoundaryGraph_le_openFaceDual G hn hlt omega

/--
[rlc_axisGapReachSet_axis_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapReachSet_axis_boundary_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_axisGapConnectorEvent G) :
-- imply
  ∃ p q : Site 2, (p, q) ∈ edgeBoundary 2 (rlc_axisGapReachSet G omega) ∧ p 0 = 0 ∧ q 0 = 0 := by
-- proof
  apply StatMech.Universality.rlc_axisGapReachSet_axis_boundary G omega hno

/--
[rlc_axisGapReachSet_axis_anchored_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapReachSet_axis_anchored_dualCircuit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_axisGapConnectorEvent G) :
-- imply
  ∃ (p q f g u : Site 2) (c : (faceBoundaryGraph (rlc_axisGapReachSet G omega)).Walk u u), (p, q) ∈ edgeBoundary 2 (rlc_axisGapReachSet G omega) ∧ p 0 = 0 ∧ q 0 = 0 ∧ (faceBoundaryGraph (rlc_axisGapReachSet G omega)).Adj f g ∧ sharedPrimalEdge f g = s(p, q) ∧ c.IsCycle ∧ s(f, g) ∈ c.edges := by
-- proof
  apply StatMech.Universality.rlc_axisGapReachSet_axis_anchored_dualCircuit G omega hno

/--
[rlc_axisGapReachSet_openFaceDualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapReachSet_openFaceDualCircuit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_axisGapConnectorEvent G) :
-- imply
  ∃ (p q f g u : Site 2) (c : (openSubgraph 2 (fci_faceDualConfig (rlc_maskConfig (rlc_axisGapEdges G) omega))).Walk u u), p 0 = 0 ∧ q 0 = 0 ∧ sharedPrimalEdge f g = s(p, q) ∧ c.IsCycle ∧ s(f, g) ∈ c.edges := by
-- proof
  apply StatMech.Universality.rlc_axisGapReachSet_openFaceDualCircuit G hn hlt omega hno

/--
[rlc_axisGapReachSet_reflectedOpenDualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapReachSet_reflectedOpenDualCircuit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_axisGapConnectorEvent G) :
-- imply
  ∃ (p q f g u : Site 2) (c : (openSubgraph 2 (rlc_dualReflectConfig (rlc_maskConfig (rlc_axisGapEdges G) omega))).Walk (rlc_dualReflect u) (rlc_dualReflect u)), p 0 = 0 ∧ q 0 = 0 ∧ sharedPrimalEdge f g = s(p, q) ∧ c.IsCycle ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∈ c.edges := by
-- proof
  apply StatMech.Universality.rlc_axisGapReachSet_reflectedOpenDualCircuit G hn hlt omega hno

/--
[rlc_axisGapConnector_half_of_dual_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_axisGapConnector_half_of_dual_reflection_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hdual : ∀ omega : ConfigSpace (Sym2 (Site 2)), omega ∉ rlc_axisGapConnectorEvent G → rlc_dualReflectConfig omega ∈ rlc_axisGapConnectorEvent G) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_axisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_axisGapConnector_half_of_dual_reflection G hdual

/--
[rlc_adaptiveConnector_half_of_dual_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_adaptiveConnector_half_of_dual_reflection_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hdual : ∀ (G : RlcAxisBarrierGap gamma gamma') (_hlt : G.lower + 1 < G.upper) (omega : ConfigSpace (Sym2 (Site 2))), omega ∉ rlc_axisGapConnectorEvent G → rlc_dualReflectConfig omega ∈ rlc_axisGapConnectorEvent G) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_adaptiveConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_adaptiveConnector_half_of_dual_reflection gamma gamma' hdual

/--
[RlcAxisBarrierGap.verticalEdge_mem_mixedAxisGapEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma verticalEdge_mem_mixedAxisGapEdges_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {t : ℤ}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hlower : G.lower ≤ t)
  (hupper : t < G.upper) :
-- imply
  s(![0, t], ![0, t + 1]) ∈ rlc_mixedAxisGapEdges G := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.verticalEdge_mem_mixedAxisGapEdges G hn hlt hlower hupper

/--
[rlc_rightPathEdges_disjoint_mixedAxisGapEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathEdges_disjoint_mixedAxisGapEdges_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  Disjoint (rlc_pathEdges gamma.1) (rlc_mixedAxisGapEdges G) := by
-- proof
  apply StatMech.Universality.rlc_rightPathEdges_disjoint_mixedAxisGapEdges G

/--
[rlc_leftPathEdges_disjoint_mixedAxisGapEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathEdges_disjoint_mixedAxisGapEdges_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  Disjoint (rlc_pathEdges gamma'.1) (rlc_mixedAxisGapEdges G) := by
-- proof
  apply StatMech.Universality.rlc_leftPathEdges_disjoint_mixedAxisGapEdges G

/--
[rlc_supportConnectorEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_supportConnectorEvent_isIncreasing_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {U : Finset (Sym2 (Site 2))} :
-- imply
  IsIncreasing (rlc_supportConnectorEvent gamma gamma' U) := by
-- proof
  apply StatMech.Universality.rlc_supportConnectorEvent_isIncreasing gamma gamma' U

/--
[rlc_supportConnectorEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_supportConnectorEvent_dependsOn_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {U : Finset (Sym2 (Site 2))} :
-- imply
  DependsOn ((rlc_supportConnectorEvent gamma gamma' U).indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_supportConnectorEvent_dependsOn gamma gamma' U

/--
[rlc_supportConnectorEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_supportConnectorEvent_measurableSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {U : Finset (Sym2 (Site 2))} :
-- imply
  MeasurableSet (rlc_supportConnectorEvent gamma gamma' U) := by
-- proof
  apply StatMech.Universality.rlc_supportConnectorEvent_measurableSet gamma gamma' U

/--
[rlc_mixedAxisGapConnectorEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedAxisGapConnectorEvent_dependsOn_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  DependsOn ((rlc_mixedAxisGapConnectorEvent G).indicator (fun _ => (1 : ℝ))) (rlc_mixedAxisGapEdges G : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_mixedAxisGapConnectorEvent_dependsOn G

/--
[rlc_mixedAxisGapConnectorEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedAxisGapConnectorEvent_measurableSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  MeasurableSet (rlc_mixedAxisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_mixedAxisGapConnectorEvent_measurableSet G

/--
[rlc_supportConnector_glues_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_supportConnector_glues_horizontal_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {U : Finset (Sym2 (Site 2))}
-- given
  (_hn : 0 < n) :
-- imply
  rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩ rlc_supportConnectorEvent gamma gamma' U ⊆ horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_supportConnector_glues_horizontal n _hn gamma gamma' U

/--
[rlc_mixedAxisGapConnector_glues_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedAxisGapConnector_glues_horizontal_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hn : 0 < n) :
-- imply
  rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩ rlc_mixedAxisGapConnectorEvent G ⊆ horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_mixedAxisGapConnector_glues_horizontal n hn gamma gamma' G

/--
[rlc_mixedAdaptiveConnectorEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedAdaptiveConnectorEvent_dependsOn_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  DependsOn ((rlc_mixedAdaptiveConnectorEvent gamma gamma').indicator (fun _ => (1 : ℝ))) (rlc_mixedAdaptiveEdges gamma gamma' : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_mixedAdaptiveConnectorEvent_dependsOn gamma gamma'

/--
[rlc_mixedAdaptiveConnectorEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedAdaptiveConnectorEvent_measurableSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  MeasurableSet (rlc_mixedAdaptiveConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_mixedAdaptiveConnectorEvent_measurableSet gamma gamma'

/--
[rlc_rightPathEdges_disjoint_mixedAdaptiveEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathEdges_disjoint_mixedAdaptiveEdges_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Disjoint (rlc_pathEdges gamma.1) (rlc_mixedAdaptiveEdges gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_rightPathEdges_disjoint_mixedAdaptiveEdges gamma gamma'

/--
[rlc_leftPathEdges_disjoint_mixedAdaptiveEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathEdges_disjoint_mixedAdaptiveEdges_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Disjoint (rlc_pathEdges gamma'.1) (rlc_mixedAdaptiveEdges gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_leftPathEdges_disjoint_mixedAdaptiveEdges gamma gamma'

/--
[rlc_mixedAdaptiveConnector_glues_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedAdaptiveConnector_glues_horizontal_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩ rlc_mixedAdaptiveConnectorEvent gamma gamma' ⊆ horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_mixedAdaptiveConnector_glues_horizontal n hn gamma gamma'

/--
[rlc_wiredConnectorConfig_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_wiredConnectorConfig_congr_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {U : Finset (Sym2 (Site 2))}
  {omega omega' : ConfigSpace (Sym2 (Site 2))}
-- given
  (hagree : ∀ e ∈ (U : Set (Sym2 (Site 2))), omega e = omega' e) :
-- imply
  rlc_wiredConnectorConfig gamma gamma' U omega = rlc_wiredConnectorConfig gamma gamma' U omega' := by
-- proof
  apply StatMech.Universality.rlc_wiredConnectorConfig_congr gamma gamma' U hagree

/--
[rlc_wiredConnectorConfig_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_wiredConnectorConfig_mono_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {U : Finset (Sym2 (Site 2))}
  {omega omega' : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : omega ≤ omega') :
-- imply
  rlc_wiredConnectorConfig gamma gamma' U omega ≤ rlc_wiredConnectorConfig gamma gamma' U omega' := by
-- proof
  apply StatMech.Universality.rlc_wiredConnectorConfig_mono gamma gamma' U h

/--
[rlc_dualReflect_wired_open_of_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_dualReflect_wired_open_of_support_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)}
-- given
  (heTarget : e ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪ rlc_mixedAxisGapEdges G)
  (heSource : rlc_pimsEdgeEquiv e ∈ rlc_mixedAxisGapEdges G)
  (hopen : rlc_dualReflectConfig (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) e = true) :
-- imply
  rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) (rlc_dualReflectConfig omega) e = true := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_wired_open_of_support G omega heTarget heSource hopen

/--
[rlc_dualReflect_wired_walk_of_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_dualReflect_wired_walk_of_support_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {p : (openSubgraph 2 (rlc_dualReflectConfig (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega))).Walk x y}
-- given
  (hsupport : ∀ e ∈ p.edges, e ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪ rlc_mixedAxisGapEdges G ∧ rlc_pimsEdgeEquiv e ∈ rlc_mixedAxisGapEdges G) :
-- imply
  ∃ q : (openSubgraph 2 (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) (rlc_dualReflectConfig omega))).Walk x y, q.edges = p.edges ∧ q.support = p.support := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_wired_walk_of_support G omega p hsupport

/--
[rlc_wiredConnectorConfig_le_of_pathOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_wiredConnectorConfig_le_of_pathOpen_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {U : Finset (Sym2 (Site 2))}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hgamma : omega ∈ rlc_pathOpen gamma.1)
  (hgamma' : omega ∈ rlc_pathOpen gamma'.1) :
-- imply
  rlc_wiredConnectorConfig gamma gamma' U omega ≤ omega := by
-- proof
  apply StatMech.Universality.rlc_wiredConnectorConfig_le_of_pathOpen gamma gamma' U omega hgamma hgamma'

/--
[rlc_mixedWiredConnectorEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_isIncreasing_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  IsIncreasing (rlc_mixedWiredConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_isIncreasing G

/--
[rlc_mixedWiredConnectorEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dependsOn_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  DependsOn ((rlc_mixedWiredConnectorEvent G).indicator (fun _ => (1 : ℝ))) (rlc_mixedAxisGapEdges G : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dependsOn G

/--
[rlc_mixedWiredConnectorEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_measurableSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  MeasurableSet (rlc_mixedWiredConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_measurableSet G

/--
[rlc_mixedWiredConnector_half_of_dual_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredConnector_half_of_dual_reflection_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hdual : ∀ omega : ConfigSpace (Sym2 (Site 2)), omega ∉ rlc_mixedWiredConnectorEvent G → rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_mixedWiredConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnector_half_of_dual_reflection G hdual

/--
[rlc_mixedWiredConnector_glues_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredConnector_glues_horizontal_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (_hn : 0 < n) :
-- imply
  rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩ rlc_mixedWiredConnectorEvent G ⊆ horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnector_glues_horizontal n _hn gamma gamma' G

/--
[rlc_wiredConnectorConfig_rightPathOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_wiredConnectorConfig_rightPathOpen_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {U : Finset (Sym2 (Site 2))}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  rlc_wiredConnectorConfig gamma gamma' U omega ∈ rlc_pathOpen gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_wiredConnectorConfig_rightPathOpen gamma gamma' U omega

/--
[rlc_wiredConnectorConfig_leftPathOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_wiredConnectorConfig_leftPathOpen_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {U : Finset (Sym2 (Site 2))}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  rlc_wiredConnectorConfig gamma gamma' U omega ∈ rlc_pathOpen gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_wiredConnectorConfig_leftPathOpen gamma gamma' U omega

/--
[rlc_maskConfig_le_wiredConnectorConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_maskConfig_le_wiredConnectorConfig_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {U : Finset (Sym2 (Site 2))}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  rlc_maskConfig U omega ≤ rlc_wiredConnectorConfig gamma gamma' U omega := by
-- proof
  apply StatMech.Universality.rlc_maskConfig_le_wiredConnectorConfig gamma gamma' U omega

/--
[rlc_mixedAxisGapConnectorEvent_subset_mixedWiredConnectorEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedAxisGapConnectorEvent_subset_mixedWiredConnectorEvent_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  rlc_mixedAxisGapConnectorEvent G ⊆ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedAxisGapConnectorEvent_subset_mixedWiredConnectorEvent G

/--
[rlc_mixedWiredReachSet_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_subset_box_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  rlc_mixedWiredReachSet G omega ⊆ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_subset_box G omega

/--
[rlc_mixedWiredReachSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_finite_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  (rlc_mixedWiredReachSet G omega).Finite := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_finite G omega

/--
[RlcAxisBarrierGap.lowerVertex_mem_mixedWiredReachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma lowerVertex_mem_mixedWiredReachSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  G.lowerVertex ∈ rlc_mixedWiredReachSet G omega := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.lowerVertex_mem_mixedWiredReachSet G omega

/--
[rlc_rightPathVertex_mem_mixedWiredReachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_rightPathVertex_mem_mixedWiredReachSet_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x : Site 2}
-- given
  (hx : x ∈ rlc_pathVertices gamma.1) :
-- imply
  x ∈ rlc_mixedWiredReachSet G omega := by
-- proof
  apply StatMech.Universality.rlc_rightPathVertex_mem_mixedWiredReachSet G omega hx

/--
[rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {y : Site 2}
-- given
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (hy : y ∈ rlc_pathVertices gamma'.1) :
-- imply
  y ∉ rlc_mixedWiredReachSet G omega := by
-- proof
  apply StatMech.Universality.rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure G omega hno hy

/--
[rlc_mixedWiredReachSet_axis_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_axis_boundary_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ p q : Site 2, (p, q) ∈ edgeBoundary 2 (rlc_mixedWiredReachSet G omega) ∧ p 0 = 0 ∧ q 0 = 0 := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_axis_boundary G omega hno

/--
[rlc_mixedWiredReachSet_verticalGap_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_verticalGap_boundary_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ t : ℤ, G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ ((![0, t], ![0, t + 1]) ∈ edgeBoundary 2 (rlc_mixedWiredReachSet G omega)) := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_verticalGap_boundary G omega hno

/--
[rlc_mem_connectorBox_flipX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mem_connectorBox_flipX_eq
  {n : ℤ}
  {z : Site 2} :
-- imply
  z ∈ rect (-2 * n) (2 * n) (-n) n ↔ rlc_flipX z ∈ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_mem_connectorBox_flipX z

/--
[rlc_reflectedRightPathEdge_endpoint_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_reflectedRightPathEdge_endpoint_mem_box_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ rlc_reflectedPathEdges gamma.1)
  (hz : z ∈ e) :
-- imply
  z ∈ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_reflectedRightPathEdge_endpoint_mem_box gamma he hz

/--
[rlc_reflectedLeftPathEdge_endpoint_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_reflectedLeftPathEdge_endpoint_mem_box_eq
  {n : ℤ}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ rlc_reflectedPathEdges gamma'.1)
  (hz : z ∈ e) :
-- imply
  z ∈ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_reflectedLeftPathEdge_endpoint_mem_box gamma' he hz

/--
[rlc_mixedAxisGapEdges_endpoints_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedAxisGapEdges_endpoints_mem_box_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {v w : Site 2}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (he : s(v, w) ∈ rlc_mixedAxisGapEdges G) :
-- imply
  v ∈ rect (-2 * n) (2 * n) (-n) n ∧ w ∈ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_mixedAxisGapEdges_endpoints_mem_box G hn hlt he

/--
[rlc_exposedPathEdges_endpoints_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_exposedPathEdges_endpoints_mem_box_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {v w : Site 2}
-- given
  (he : s(v, w) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  v ∈ rect (-2 * n) (2 * n) (-n) n ∧ w ∈ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_exposedPathEdges_endpoints_mem_box he

/--
[rlc_mixedWiredReachSet_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_extend_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {v w : Site 2}
-- given
  (hv : v ∈ rlc_mixedWiredReachSet G omega)
  (hwR : w ∈ rect (-2 * n) (2 * n) (-n) n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hopen : rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega s(v, w) = true) :
-- imply
  w ∈ rlc_mixedWiredReachSet G omega := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_extend G omega hv hwR hadj hopen

/--
[rlc_mixedWiredReachSet_boundary_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_boundary_closed_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {v w : Site 2}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hv : v ∈ rlc_mixedWiredReachSet G omega)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hw : w ∉ rlc_mixedWiredReachSet G omega) :
-- imply
  rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega s(v, w) = false := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_boundary_closed G hn hlt omega hv hadj hw

/--
[rlc_mixedWiredReachSet_edgeBoundary_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_edgeBoundary_closed_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {v w : Site 2}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hvw : (v, w) ∈ edgeBoundary 2 (rlc_mixedWiredReachSet G omega)) :
-- imply
  rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega s(v, w) = false := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_edgeBoundary_closed G hn hlt omega hvw

/--
[rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper) :
-- imply
  faceBoundaryGraph (rlc_mixedWiredReachSet G omega) ≤ openSubgraph 2 (fci_faceDualConfig (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega)) := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega

/--
[rlc_mixedWiredReachSet_axis_anchored_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_axis_anchored_dualCircuit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ (t : ℤ) (f g u : Site 2) (c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u u), G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧ sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧ c.IsCycle ∧ s(f, g) ∈ c.edges := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_axis_anchored_dualCircuit G omega hno

/--
[rlc_mixedWiredReachSet_openFaceDualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_openFaceDualCircuit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ (t : ℤ) (f g u : Site 2) (c : (openSubgraph 2 (fci_faceDualConfig (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega))).Walk u u), G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ (hypercubicLattice 2).Adj f g ∧ sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧ c.IsCycle ∧ s(f, g) ∈ c.edges := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_openFaceDualCircuit G hn hlt omega hno

/--
[rlc_mixedWiredReachSet_reflectedOpenDualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_reflectedOpenDualCircuit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ (t : ℤ) (u : Site 2) (c : (openSubgraph 2 (rlc_dualReflectConfig (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega))).Walk (rlc_dualReflect u) (rlc_dualReflect u)), G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ c.IsCycle ∧ s(![-1, t + 1], ![0, t + 1]) ∈ c.edges := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_reflectedOpenDualCircuit G hn hlt omega hno

/--
[rlc_mixedWiredReachSet_reflectedOpenDualComplementaryArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_reflectedOpenDualComplementaryArc_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ t : ℤ, G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ ∃ p : (openSubgraph 2 (rlc_dualReflectConfig (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega))).Walk ![-1, t + 1] ![0, t + 1], s(![-1, t + 1], ![0, t + 1]) ∉ p.edges := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_reflectedOpenDualComplementaryArc G hn hlt omega hno

/--
[rlc_mixedWiredFailure_reflectedAnchor_open_raw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean)
-/
@[path]
private lemma rlc_mixedWiredFailure_reflectedAnchor_open_raw_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ t : ℤ, G.lower ≤ t ∧ t < G.upper ∧ rlc_dualReflectConfig omega s(![-1, t + 1], ![0, t + 1]) = true := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredFailure_reflectedAnchor_open_raw G hn hlt omega hno


-- created on 2026-10-23
