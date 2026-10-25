import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Foundations.StrassenFull.Part7
open MeasureTheory Finset StatMech StatMech.Transport


/--
[isClosed_nonneg_smul_of_compact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean)
-/
@[path]
private lemma isClosed_nonneg_smul_of_compact_eq
  [NormedAddCommGroup H]
  [NormedSpace ℝ H]
  {K : Set H}
-- given
  (hK : IsCompact K)
  (h0 : (0 : H) ∉ K) :
-- imply
  IsClosed {z : H | ∃ t : ℝ, 0 ≤ t ∧ ∃ x ∈ K, z = t • x} := by
-- proof
  apply StatMech.Transport.isClosed_nonneg_smul_of_compact K hK h0

/--
[layer_cake](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean)
-/
@[path]
private lemma layer_cake_eq
  [Fintype P]
  [DecidableEq P]
  [PartialOrder P]
  [Nonempty P]
  {g : P → ℝ}
-- given
  (h : P → ℝ)
  (hanti : Antitone h)
  (hpos : ∀ x, 0 ≤ h x)
  (hg : ∀ D : Finset P, IsDown D → 0 ≤ ∑ x ∈ D, g x) :
-- imply
  0 ≤ ∑ x, g x * h x := by
-- proof
  apply StatMech.Transport.layer_cake g h hanti hpos hg

/--
[dual_feasibility](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean)
-/
@[path]
private lemma dual_feasibility_eq
  [Fintype P]
  [DecidableEq P]
  [PartialOrder P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]
  [Nonempty P]
  {μ ν : P → ℝ}
  {φ ψ : P → ℝ}
-- given
  (hμpos : ∀ x, 0 ≤ μ x)
  (hνpos : ∀ x, 0 ≤ ν x)
  (hTOT : ∑ x, μ x = ∑ x, ν x)
  (hDOM : ∀ D : Finset P, IsDown D → ∑ x ∈ D, ν x ≤ ∑ x ∈ D, μ x)
  (hfeas : ∀ x y, x ≤ y → 0 ≤ φ x + ψ y) :
-- imply
  0 ≤ (∑ x, μ x * φ x) + ∑ y, ν y * ψ y := by
-- proof
  apply StatMech.Transport.dual_feasibility μ ν hμpos hνpos hTOT hDOM φ ψ hfeas

/--
[margCLM_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean)
-/
@[path]
private lemma margCLM_inl_eq
  [Fintype P]
  [DecidableEq P]
  [PartialOrder P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]
  {c : EuclideanSpace ℝ (OrderPairs P)}
  {x : P} :
-- imply
  margCLM c (Sum.inl x) = ∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0 := by
-- proof
  apply StatMech.Transport.margCLM_inl c x

/--
[margCLM_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean)
-/
@[path]
private lemma margCLM_inr_eq
  [Fintype P]
  [DecidableEq P]
  [PartialOrder P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]
  {c : EuclideanSpace ℝ (OrderPairs P)}
  {y : P} :
-- imply
  margCLM c (Sum.inr y) = ∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0 := by
-- proof
  apply StatMech.Transport.margCLM_inr c y

/--
[marg_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean)
-/
@[path]
private lemma marg_inner_eq
  [Fintype P]
  [DecidableEq P]
  [PartialOrder P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]
  {c : EuclideanSpace ℝ (OrderPairs P)}
  {w : EuclideanSpace ℝ (P ⊕ P)} :
-- imply
  (inner ℝ (margCLM c) w : ℝ) = ∑ q : OrderPairs P, c q * (w (Sum.inl (q : P × P).1) + w (Sum.inr (q : P × P).2)) := by
-- proof
  apply StatMech.Transport.marg_inner c w

/--
[mem_orthant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean)
-/
@[path]
private lemma mem_orthant_eq
  [Fintype P]
  [DecidableEq P]
  [PartialOrder P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]
  {y : EuclideanSpace ℝ (OrderPairs P)} :
-- imply
  y ∈ orthant P ↔ ∀ q, 0 ≤ y q := by
-- proof
  apply StatMech.Transport.mem_orthant y

/--
[inner_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean)
-/
@[path]
private lemma inner_eq_sum_eq
  [Fintype P]
  [DecidableEq P]
  [PartialOrder P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]
  {x y : EuclideanSpace ℝ (OrderPairs P)} :
-- imply
  (inner ℝ x y : ℝ) = ∑ q, x q * y q := by
-- proof
  apply StatMech.Transport.inner_eq_sum x y

/--
[orthant_selfdual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean)
-/
@[path]
private lemma orthant_selfdual_eq
  [Fintype P]
  [DecidableEq P]
  [PartialOrder P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)] :
-- imply
  innerDual ((orthant P : Set (EuclideanSpace ℝ (OrderPairs P)))) = orthant P := by
-- proof
  apply StatMech.Transport.orthant_selfdual

/--
[exists_coupling_vec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean)
-/
@[path]
private lemma exists_coupling_vec_eq
  [Fintype P]
  [DecidableEq P]
  [PartialOrder P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]
  [Nonempty P]
  {μ ν : P → ℝ}
-- given
  (hμpos : ∀ x, 0 ≤ μ x)
  (hνpos : ∀ x, 0 ≤ ν x)
  (hTOT : ∑ x, μ x = ∑ x, ν x)
  (hDOM : ∀ D : Finset P, IsDown D → ∑ x ∈ D, ν x ≤ ∑ x ∈ D, μ x) :
-- imply
  ∃ c : OrderPairs P → ℝ, (∀ q, 0 ≤ c q) ∧ (∀ x, (∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0) = μ x) ∧ (∀ y, (∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0) = ν y) := by
-- proof
  apply StatMech.Transport.exists_coupling_vec μ ν hμpos hνpos hTOT hDOM

/--
[exists_monotoneCoupling_of_stochasticallyDominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean)
-/
@[path]
private lemma exists_monotoneCoupling_of_stochasticallyDominated_eq
  [Fintype E]
  [DecidableEq E]
  {μ ν : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν]
-- given
  (hdom : μ ≼ ν) :
-- imply
  ∃ κ : Measure (ConfigSpace E × ConfigSpace E), IsFiniteMeasure κ ∧ MonotoneCoupling μ ν κ := by
-- proof
  apply StatMech.exists_monotoneCoupling_of_stochasticallyDominated μ ν hdom


-- created on 2026-10-23
