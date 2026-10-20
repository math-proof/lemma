/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/PermutationStability.lean -/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Solvable
import Mathlib.InformationTheory.Hamming
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Permutation stability of groups

Normalized and flexible Hamming distances between permutations, almost-homomorphisms,
and (flexible) permutation stability, following Kourovka Notebook 21.84.
-/

namespace PermutationStability

/-- Normalized Hamming distance between two permutations of `Fin n`: the
fraction of points on which they disagree. At `n = 0` the denominator is zero,
so the quotient is `0` by the `ZeroInv₀` convention; this single value is
harmless for `Filter.atTop` convergence statements. -/
noncomputable def normalizedHammingDistance (n : ℕ) (σ τ : Equiv.Perm (Fin n)) : ℝ :=
  (hammingDist (fun i => σ i) (fun i => τ i) : ℝ) / n

/-- A sequence of (arbitrary) set maps `f n : G → Equiv.Perm (Fin n)` is an
almost-homomorphism when the normalized Hamming defect
`d(f n g * f n h, f n (g * h))` tends to zero for every pair `g h`.
Following the source, no condition such as `f n 1 = 1` is imposed. -/
def IsAlmostHomomorphism {G : Type*} [Group G]
    (f : ∀ n : ℕ, G → Equiv.Perm (Fin n)) : Prop :=
  ∀ g h : G, Filter.Tendsto
    (fun n => normalizedHammingDistance n (f n g * f n h) (f n (g * h)))
    Filter.atTop (nhds 0)

/-- `f` is close to homomorphisms when genuine homomorphisms
`ρ n : G →* Equiv.Perm (Fin n)` pointwise approximate it in normalized
Hamming distance, uniformly over each fixed `g` along `Filter.atTop`. -/
def IsCloseToHomomorphisms {G : Type*} [Group G]
    (f : ∀ n : ℕ, G → Equiv.Perm (Fin n)) : Prop :=
  ∃ ρ : ∀ n : ℕ, G →* Equiv.Perm (Fin n), ∀ g : G, Filter.Tendsto
    (fun n => normalizedHammingDistance n (ρ n g) (f n g))
    Filter.atTop (nhds 0)

/-- `G` is permutation stable when every almost-homomorphism is close to
genuine homomorphisms. -/
def PermutationStable (G : Type*) [Group G] : Prop :=
  ∀ f : ∀ n : ℕ, G → Equiv.Perm (Fin n),
    IsAlmostHomomorphism f → IsCloseToHomomorphisms f

/-- Flexible Hamming distance between a small permutation `σ` of `Fin n` and a
large permutation `τ` of `Fin m` (with `h : n ≤ m`): the disagreement count on
the embedded copy plus the `m - n` unmatched points, normalized by `n`.

Kourovka 21.84 is internally inconsistent about the argument order: it first
defines the distance with the small permutation first, `d_n^flex(σ, τ)` for
`σ ∈ S_n`, `τ ∈ S_m`, but later writes the convergence expression with
`ρ_n(g)` first. This formalization follows the definition site (small first),
which is also the type-correct order for the embedding `Fin n → Fin m`.

As above, the `n = 0` denominator is harmless for `Filter.atTop`
convergence. -/
noncomputable def flexibleHammingDistance {n m : ℕ} (h : n ≤ m)
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) : ℝ :=
  ((hammingDist (fun i => Fin.castLE h (σ i))
      (fun i => τ (Fin.castLE h i)) + (m - n) : ℕ) : ℝ) / n

/-- `f` is flexibly close to homomorphisms when, after embedding each `Fin n`
into some `Fin (m n)`, genuine homomorphisms `ρ n` approximate `f` in the
flexible Hamming distance for every fixed `g` along `Filter.atTop`. -/
def IsFlexiblyCloseToHomomorphisms {G : Type*} [Group G]
    (f : ∀ n : ℕ, G → Equiv.Perm (Fin n)) : Prop :=
  ∃ m : ℕ → ℕ, ∃ h : ∀ n : ℕ, n ≤ m n,
    ∃ ρ : ∀ n : ℕ, G →* Equiv.Perm (Fin (m n)), ∀ g : G, Filter.Tendsto
      (fun n => flexibleHammingDistance (h n) (f n g) (ρ n g))
      Filter.atTop (nhds 0)

/-- `G` is flexibly permutation stable when every almost-homomorphism is
flexibly close to genuine homomorphisms. -/
def FlexiblePermutationStable (G : Type*) [Group G] : Prop :=
  ∀ f : ∀ n : ℕ, G → Equiv.Perm (Fin n),
    IsAlmostHomomorphism f → IsFlexiblyCloseToHomomorphisms f

/-- `G` is metabelian when its second derived subgroup is trivial. -/
def Metabelian (G : Type*) [Group G] : Prop :=
  derivedSeries G 2 = ⊥

theorem normalizedHammingDistance_self (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    normalizedHammingDistance n σ σ = 0 := by
  simp [normalizedHammingDistance]

theorem normalizedHammingDistance_nonneg (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    0 ≤ normalizedHammingDistance n σ τ := by
  unfold normalizedHammingDistance
  positivity

theorem normalizedHammingDistance_le_one {n : ℕ} (hn : 0 < n)
    (σ τ : Equiv.Perm (Fin n)) :
    normalizedHammingDistance n σ τ ≤ 1 := by
  unfold normalizedHammingDistance
  rw [div_le_one (Nat.cast_pos.mpr hn)]
  have h := hammingDist_le_card_fintype (x := fun i => σ i) (y := fun i => τ i)
  rw [Fintype.card_fin] at h
  exact Nat.cast_le.mpr h

theorem flexibleHammingDistance_self {n m : ℕ} (h : n ≤ m)
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m))
    (hτ : ∀ i, τ (Fin.castLE h i) = Fin.castLE h (σ i)) :
    flexibleHammingDistance h σ τ = ((m - n : ℕ) : ℝ) / n := by
  have hfun : (fun i => τ (Fin.castLE h i)) = (fun i => Fin.castLE h (σ i)) :=
    funext hτ
  unfold flexibleHammingDistance
  rw [hfun, hammingDist_self, Nat.zero_add]

theorem flexibleHammingDistance_diagonal {n : ℕ} (h : n ≤ n)
    (σ τ : Equiv.Perm (Fin n)) :
    flexibleHammingDistance h σ τ = normalizedHammingDistance n σ τ := by
  have hfun : (fun i => Fin.castLE h (σ i)) = (fun i => σ i) :=
    funext fun i => Fin.ext rfl
  have hfun' : (fun i => τ (Fin.castLE h i)) = (fun i => τ i) :=
    funext fun i => congrArg (τ ·) (Fin.ext rfl)
  unfold flexibleHammingDistance normalizedHammingDistance
  rw [hfun, hfun', Nat.sub_self, Nat.add_zero]

end PermutationStability
