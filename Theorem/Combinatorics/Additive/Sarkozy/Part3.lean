/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Basic
import Def.Combinatorics.Additive.Sarkozy.Part4


namespace MathlibExt.Combinatorics.Additive.SarkozyWanted

open scoped InnerProductSpace

/-- The inner sum extends by zero to any larger finite index set. -/
theorem sarkozyToepInnerAux_extend (γ : ℤ → ℝ) (cf df : ℤ →₀ ℝ)
    (t : Finset ℤ) (hsub : cf.support ⊆ t) :
    sarkozyToepInnerAux γ cf df
      = ∑ i ∈ t, ∑ j ∈ df.support, cf i * df j * γ (i - j) := by
  simp only [sarkozyToepInnerAux]
  exact Finset.sum_subset hsub (fun i _ hi =>
    Finset.sum_eq_zero (fun j _ => by
      rw [Finsupp.notMem_support_iff.mp hi]
      ring))

/-- Additivity of the Toeplitz inner product in the first slot. -/
theorem sarkozyToepInnerAux_add_left (γ : ℤ → ℝ) (c₁ c₂ d : ℤ →₀ ℝ) :
    sarkozyToepInnerAux γ (c₁ + c₂) d
      = sarkozyToepInnerAux γ c₁ d + sarkozyToepInnerAux γ c₂ d := by
  rw [sarkozyToepInnerAux_extend γ (c₁ + c₂) d (c₁.support ∪ c₂.support)
      Finsupp.support_add,
    sarkozyToepInnerAux_extend γ c₁ d (c₁.support ∪ c₂.support)
      Finset.subset_union_left,
    sarkozyToepInnerAux_extend γ c₂ d (c₁.support ∪ c₂.support)
      Finset.subset_union_right]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finsupp.add_apply]
  trans ∑ j ∈ d.support, ((c₁ i * d j * γ (i - j)) + (c₂ i * d j * γ (i - j)))
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · exact Finset.sum_add_distrib

/-- Homogeneity of the Toeplitz inner product in the first slot. -/
theorem sarkozyToepInnerAux_smul_left (γ : ℤ → ℝ) (r : ℝ) (c d : ℤ →₀ ℝ) :
    sarkozyToepInnerAux γ (r • c) d = r * sarkozyToepInnerAux γ c d := by
  rw [sarkozyToepInnerAux_extend γ (r • c) d c.support Finsupp.support_smul]
  simp only [sarkozyToepInnerAux]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finsupp.smul_apply, smul_eq_mul]
  ring

/-- Symmetry of the Toeplitz inner product. -/
theorem sarkozyToepInnerAux_symm (γ : ℤ → ℝ) (hsymm : ∀ d, γ (-d) = γ d)
    (c d : ℤ →₀ ℝ) :
    sarkozyToepInnerAux γ d c = sarkozyToepInnerAux γ c d := by
  simp only [sarkozyToepInnerAux]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hγ : γ (j - i) = γ (i - j) := by
    have h : j - i = -(i - j) := by ring
    rw [h]
    exact hsymm (i - j)
  rw [hγ]
  ring

/-- The inner product of basis vectors recovers `γ`. -/
theorem sarkozyToepInnerAux_single (γ : ℤ → ℝ) (m n : ℤ) :
    sarkozyToepInnerAux γ (Finsupp.single m 1) (Finsupp.single n 1)
      = γ (m - n) := by
  simp only [sarkozyToepInnerAux]
  rw [Finsupp.support_single _ one_ne_zero, Finsupp.support_single _ one_ne_zero,
    Finset.sum_singleton, Finset.sum_singleton, Finsupp.single_apply,
    Finsupp.single_apply]
  simp

/-- Nonnegativity on the diagonal from positive semidefiniteness. -/
theorem sarkozyToepInnerAux_nonneg (γ : ℤ → ℝ)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j))
    (c : ℤ →₀ ℝ) : 0 ≤ sarkozyToepInnerAux γ c c := by
  simp only [sarkozyToepInnerAux]
  exact hpos _ _

/-- The shift preserves the Toeplitz inner product. -/
theorem sarkozyShift_inner_aux (γ : ℤ → ℝ) (c d : ℤ →₀ ℝ) :
    sarkozyToepInnerAux γ (Finsupp.mapDomain (fun i : ℤ => i + 1) c)
      (Finsupp.mapDomain (fun i : ℤ => i + 1) d)
      = sarkozyToepInnerAux γ c d := by
  have hinj : Function.Injective (fun i : ℤ => i + 1) := by
    intro a b h
    simpa using h
  have hsup1 : (Finsupp.mapDomain (fun i : ℤ => i + 1) c).support
      = Finset.image (fun i : ℤ => i + 1) c.support :=
    Finsupp.mapDomain_support_of_injective hinj c
  have hsup2 : (Finsupp.mapDomain (fun i : ℤ => i + 1) d).support
      = Finset.image (fun i : ℤ => i + 1) d.support :=
    Finsupp.mapDomain_support_of_injective hinj d
  have happ : ∀ a : ℤ, (Finsupp.mapDomain (fun i : ℤ => i + 1) c) (a + 1) = c a := by
    intro a
    exact Finsupp.mapDomain_apply' Set.univ _ (Set.subset_univ _)
      hinj.injOn (Set.mem_univ a)
  have happd : ∀ b : ℤ, (Finsupp.mapDomain (fun i : ℤ => i + 1) d) (b + 1) = d b := by
    intro b
    exact Finsupp.mapDomain_apply' Set.univ _ (Set.subset_univ _)
      hinj.injOn (Set.mem_univ b)
  have hdiff : ∀ a b : ℤ, (a + 1) - (b + 1) = a - b := fun a b => by ring
  simp only [sarkozyToepInnerAux, hsup1, hsup2]
  rw [Finset.sum_image hinj.injOn]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_image hinj.injOn]
  apply Finset.sum_congr rfl
  intro b _
  simp only [happ a, happd b, hdiff a b]

end MathlibExt.Combinatorics.Additive.SarkozyWanted
