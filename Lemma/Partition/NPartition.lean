import Mathlib
import sympy.Basic
import sympy.combinatorics.partitions.NPartition
open NPartition
open Finset
open scoped BigOperators


/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_isNPartition_iff_antitone
-- given
  {N : ℕ}
  {lam : Fin N → ℕ} :
-- imply
  IsNPartition lam ↔ Antitone lam := by
-- proof
  apply isNPartition_iff_antitone

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_isNPartition_zero
-- given
  {N : ℕ} :
-- imply
  IsNPartition (0 : Fin N → ℕ) := by
-- proof
  apply isNPartition_zero

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma add
-- given
  {N : ℕ}
  {α β : Fin N → ℕ}
  (hα : IsNPartition α)
  (hβ : IsNPartition β) :
-- imply
  IsNPartition (α + β) := by
-- proof
  apply IsNPartition.add hα hβ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma monotone
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  ∀ i j : Fin N, i ≤ j → μ.parts j ≤ μ.parts i := by
-- proof
  apply NPartition.monotone μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma weaklyDecreasing
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  ∀ i j : Fin N, i ≤ j → μ.parts j ≤ μ.parts i := by
-- proof
  apply NPartition.weaklyDecreasing μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma parts_antitone
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  Antitone μ.parts := by
-- proof
  apply NPartition.parts_antitone μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma isNPartition
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  IsNPartition μ.parts := by
-- proof
  apply NPartition.isNPartition μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma ext
-- given
  {N : ℕ}
  {μ ν : NPartition N}
  (h : μ.parts = ν.parts) :
-- imply
  μ = ν := by
-- proof
  apply NPartition.ext h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma ext'
-- given
  {N : ℕ}
  {μ ν : NPartition N} :
-- imply
  μ = ν ↔ ∀ i, μ.parts i = ν.parts i := by
-- proof
  apply NPartition.ext'

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma ext_parts
-- given
  {N : ℕ}
  {μ ν : NPartition N}
  (h : ∀ i, μ.parts i = ν.parts i) :
-- imply
  μ = ν := by
-- proof
  apply NPartition.ext_parts h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma parts_ext_iff
-- given
  {N : ℕ}
  {μ ν : NPartition N} :
-- imply
  μ = ν ↔ μ.parts = ν.parts := by
-- proof
  apply NPartition.parts_ext_iff

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma zero_parts
-- given
  {N : ℕ} :
-- imply
  (0 : NPartition N).parts = fun _ => 0 := by
-- proof
  apply NPartition.zero_parts

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma zero_parts_apply
-- given
  {N : ℕ}
  (i : Fin N) :
-- imply
  (0 : NPartition N).parts i = 0 := by
-- proof
  apply NPartition.zero_parts_apply i

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma size_eq_sum
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  μ.size = ∑ i, μ.parts i := by
-- proof
  apply NPartition.size_eq_sum μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma zero_size
-- given
  {N : ℕ} :
-- imply
  (0 : NPartition N).size = 0 := by
-- proof
  apply NPartition.zero_size

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma parts_le_size
-- given
  {N : ℕ}
  (μ : NPartition N)
  (i : Fin N) :
-- imply
  μ.parts i ≤ μ.size := by
-- proof
  apply NPartition.parts_le_size μ i

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma parts_zero_max
-- given
  {N : ℕ}
  (hN : 0 < N)
  (μ : NPartition N)
  (i : Fin N) :
-- imply
  μ.parts i ≤ μ.parts ⟨0, hN⟩ := by
-- proof
  apply NPartition.parts_zero_max μ i hN

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma parts_zero_eq_size_iff
-- given
  {N : ℕ}
  (hN : 0 < N)
  (μ : NPartition N) :
-- imply
  μ.parts ⟨0, hN⟩ = μ.size ↔ ∀ i : Fin N, i.val ≠ 0 → μ.parts i = 0 := by
-- proof
  apply NPartition.parts_zero_eq_size_iff μ hN

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma eq_zero_of_size_eq_zero
-- given
  {N : ℕ}
  (μ : NPartition N)
  (h : μ.size = 0) :
-- imply
  μ = 0 := by
-- proof
  apply NPartition.eq_zero_of_size_eq_zero μ h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma size_eq_zero_iff
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  μ.size = 0 ↔ μ = 0 := by
-- proof
  apply NPartition.size_eq_zero_iff μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma size_pos_of_ne_zero
-- given
  {N : ℕ}
  {μ : NPartition N}
  (h : μ ≠ 0) :
-- imply
  0 < μ.size := by
-- proof
  apply NPartition.size_pos_of_ne_zero h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma add_parts
-- given
  {N : ℕ}
  (μ ν : NPartition N)
  (i : Fin N) :
-- imply
  (μ + ν).parts i = μ.parts i + ν.parts i := by
-- proof
  apply NPartition.add_parts μ ν i

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma add_size
-- given
  {N : ℕ}
  (μ ν : NPartition N) :
-- imply
  (μ + ν).size = μ.size + ν.size := by
-- proof
  apply NPartition.add_size μ ν

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_add_comm
-- given
  {N : ℕ}
  (μ ν : NPartition N) :
-- imply
  μ + ν = ν + μ := by
-- proof
  apply NPartition.add_comm μ ν

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_add_zero
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  μ + 0 = μ := by
-- proof
  apply NPartition.add_zero μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_zero_add
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  0 + μ = μ := by
-- proof
  apply NPartition.zero_add μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_add_assoc
-- given
  {N : ℕ}
  (μ ν ρ : NPartition N) :
-- imply
  μ + ν + ρ = μ + (ν + ρ) := by
-- proof
  apply NPartition.add_assoc μ ν ρ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma coe_parts
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  (μ : Fin N → ℕ) = μ.parts := by
-- proof
  apply NPartition.coe_parts μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma le_def
-- given
  {N : ℕ}
  (μ ν : NPartition N) :
-- imply
  μ ≤ ν ↔ ∀ i, μ.parts i ≤ ν.parts i := by
-- proof
  apply NPartition.le_def μ ν

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma le_iff
-- given
  {N : ℕ}
  {μ ν : NPartition N} :
-- imply
  μ ≤ ν ↔ ∀ i, μ.parts i ≤ ν.parts i := by
-- proof
  apply NPartition.le_iff

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma mem_partitionsOfSize
-- given
  {N : ℕ}
  (μ : NPartition N)
  (n : ℕ) :
-- imply
  μ ∈ partitionsOfSize n ↔ μ.size = n := by
-- proof
  apply NPartition.mem_partitionsOfSize μ n

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma finite_of_size
-- given
  {N : ℕ}
  (n : ℕ) :
-- imply
  Set.Finite { μ : NPartition N | μ.size = n } := by
-- proof
  apply NPartition.finite_of_size n

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma np_zero_le
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  (0 : NPartition N) ≤ μ := by
-- proof
  apply NPartition.zero_le μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma size_le_of_le
-- given
  {N : ℕ}
  {μ ν : NPartition N}
  (h : μ ≤ ν) :
-- imply
  μ.size ≤ ν.size := by
-- proof
  apply NPartition.size_le_of_le h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma zero_length
-- given
  {N : ℕ} :
-- imply
  (0 : NPartition N).length = 0 := by
-- proof
  apply NPartition.zero_length

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma length_eq_zero_iff
-- given
  {N : ℕ}
  {μ : NPartition N} :
-- imply
  μ.length = 0 ↔ μ = 0 := by
-- proof
  apply NPartition.length_eq_zero_iff

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma length_pos_of_ne_zero
-- given
  {N : ℕ}
  {μ : NPartition N}
  (h : μ ≠ 0) :
-- imply
  0 < μ.length := by
-- proof
  apply NPartition.length_pos_of_ne_zero h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma length_le
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  μ.length ≤ N := by
-- proof
  apply NPartition.length_le μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma finite_support
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  Set.Finite {i | μ.parts i ≠ 0} := by
-- proof
  apply NPartition.finite_support μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma mk'_parts
-- given
  {N : ℕ}
  (parts : Fin N → ℕ)
  (h : ∀ i j : Fin N, i ≤ j → parts j ≤ parts i) :
-- imply
  (mk' parts h).parts = parts := by
-- proof
  apply NPartition.mk'_parts parts h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma mk'_antitone
-- given
  {N : ℕ}
  (parts : Fin N → ℕ)
  (h : ∀ i j : Fin N, i ≤ j → parts j ≤ parts i) :
-- imply
  (mk' parts h).antitone = h := by
-- proof
  apply NPartition.mk'_antitone parts h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma part_eq_parts
-- given
  {N : ℕ}
  (μ : NPartition N)
  (i : Fin N) :
-- imply
  μ.part i = μ.parts i := by
-- proof
  apply NPartition.part_eq_parts μ i

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma ofPartition_size
-- given
  {N n : ℕ}
  (p : Nat.Partition n)
  (hp : Multiset.card p.parts ≤ N) :
-- imply
  (ofPartition p hp).size = n := by
-- proof
  apply NPartition.ofPartition_size p hp

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma toPartition_card_le
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  Multiset.card μ.toPartition.parts ≤ N := by
-- proof
  apply NPartition.toPartition_card_le μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma mem_youngDiagram
-- given
  {N : ℕ}
  {μ : NPartition N}
  {c : Fin N × ℕ} :
-- imply
  c ∈ μ.youngDiagram ↔ c.2 < μ.parts c.1 := by
-- proof
  apply NPartition.mem_youngDiagram

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma mem_youngDiagram'
-- given
  {N : ℕ}
  {μ : NPartition N}
  {i : Fin N}
  {j : ℕ} :
-- imply
  (i, j) ∈ μ.youngDiagram ↔ j < μ.parts i := by
-- proof
  apply NPartition.mem_youngDiagram'

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma youngDiagram_eq_empty_iff
-- given
  {N : ℕ}
  {μ : NPartition N} :
-- imply
  μ.youngDiagram = ∅ ↔ μ = 0 := by
-- proof
  apply NPartition.youngDiagram_eq_empty_iff

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma youngDiagram_nonempty_iff
-- given
  {N : ℕ}
  {μ : NPartition N} :
-- imply
  μ.youngDiagram.Nonempty ↔ μ ≠ 0 := by
-- proof
  apply NPartition.youngDiagram_nonempty_iff

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma youngDiagram_row_card
-- given
  {N : ℕ}
  (μ : NPartition N)
  (i : Fin N) :
-- imply
  (μ.youngDiagram.filter fun c => c.1 = i).card = μ.parts i := by
-- proof
  apply NPartition.youngDiagram_row_card μ i

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma youngDiagram_snd_lt_parts
-- given
  {N : ℕ}
  {μ : NPartition N}
  {c : Fin N × ℕ}
  (h : c ∈ μ.youngDiagram) :
-- imply
  c.2 < μ.parts c.1 := by
-- proof
  apply NPartition.youngDiagram_snd_lt_parts h

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma youngDiagram_subset_prod
-- given
  {N : ℕ}
  (hN : 0 < N)
  (μ : NPartition N) :
-- imply
  μ.youngDiagram ⊆ Finset.univ ×ˢ Finset.range (μ.parts ⟨0, hN⟩) := by
-- proof
  apply NPartition.youngDiagram_subset_prod μ hN

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma youngDiagram_subset_prod'
  {N : ℕ} [NeZero N]
-- given
  (μ : NPartition N) :
-- imply
  μ.youngDiagram ⊆ Finset.univ ×ˢ Finset.range (μ.parts 0) := by
-- proof
  apply NPartition.youngDiagram_subset_prod' μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma mem_youngDiagram_zero_col
-- given
  {N : ℕ}
  {μ : NPartition N}
  {i : Fin N} :
-- imply
  (i, 0) ∈ μ.youngDiagram ↔ 0 < μ.parts i := by
-- proof
  apply NPartition.mem_youngDiagram_zero_col

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma youngDiagram_card
-- given
  {N : ℕ}
  (μ : NPartition N) :
-- imply
  μ.youngDiagram.card = μ.size := by
-- proof
  apply NPartition.youngDiagram_card μ

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma youngDiagram_zero
-- given
  {N : ℕ} :
-- imply
  (0 : NPartition N).youngDiagram = ∅ := by
-- proof
  apply NPartition.youngDiagram_zero

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma le_iff_youngDiagram_subset
-- given
  {N : ℕ}
  {μ ν : NPartition N} :
-- imply
  μ ≤ ν ↔ μ.youngDiagram ⊆ ν.youngDiagram := by
-- proof
  apply NPartition.le_iff_youngDiagram_subset

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma mem_skewYoungDiagram
-- given
  {N : ℕ}
  {lam mu : NPartition N}
  {c : Fin N × ℕ} :
-- imply
  c ∈ skewYoungDiagram lam mu ↔ mu.parts c.1 ≤ c.2 ∧ c.2 < lam.parts c.1 := by
-- proof
  apply NPartition.mem_skewYoungDiagram

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma mem_skewYoungDiagram'
-- given
  {N : ℕ}
  {lam mu : NPartition N}
  {i : Fin N}
  {j : ℕ} :
-- imply
  (i, j) ∈ skewYoungDiagram lam mu ↔ j ∈ Finset.Ico (mu.parts i) (lam.parts i) := by
-- proof
  apply NPartition.mem_skewYoungDiagram'

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma skewYoungDiagram_self
-- given
  {N : ℕ}
  (lam : NPartition N) :
-- imply
  skewYoungDiagram lam lam = ∅ := by
-- proof
  apply NPartition.skewYoungDiagram_self lam

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma skewYoungDiagram_zero'
-- given
  {N : ℕ}
  (lam : NPartition N) :
-- imply
  skewYoungDiagram lam 0 = lam.youngDiagram := by
-- proof
  apply NPartition.skewYoungDiagram_zero' lam

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma skewYoungDiagram_subset_youngDiagram
-- given
  {N : ℕ}
  (lam mu : NPartition N) :
-- imply
  skewYoungDiagram lam mu ⊆ lam.youngDiagram := by
-- proof
  apply NPartition.skewYoungDiagram_subset_youngDiagram lam mu

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma skewYoungDiagram_card
-- given
  {N : ℕ}
  (lam mu : NPartition N) :
-- imply
  (skewYoungDiagram lam mu).card = ∑ i, (lam.parts i - mu.parts i) := by
-- proof
  apply NPartition.skewYoungDiagram_card lam mu

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma skewYoungDiagram_eq_empty_iff
-- given
  {N : ℕ}
  {lam mu : NPartition N} :
-- imply
  skewYoungDiagram lam mu = ∅ ↔ ∀ i, lam.parts i ≤ mu.parts i := by
-- proof
  apply NPartition.skewYoungDiagram_eq_empty_iff

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma rowPartition_size
-- given
  (N : ℕ)
  (hN : 0 < N)
  (n : ℕ) :
-- imply
  (rowPartition N n hN).size = n := by
-- proof
  apply NPartition.rowPartition_size N n hN

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma rowPartition_parts_zero
-- given
  (N : ℕ)
  (hN : 0 < N)
  (n : ℕ) :
-- imply
  (rowPartition N n hN).parts ⟨0, hN⟩ = n := by
-- proof
  apply NPartition.rowPartition_parts_zero N n hN

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma rowPartition_parts_pos
-- given
  (N : ℕ)
  (i : Fin N)
  (hN : 0 < N)
  (hi : 0 < i.val)
  (n : ℕ) :
-- imply
  (rowPartition N n hN).parts i = 0 := by
-- proof
  apply NPartition.rowPartition_parts_pos N n hN i hi

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma card_filter_fin_val_lt
-- given
  (N n : ℕ)
  (hn : n ≤ N) :
-- imply
  (Finset.univ.filter (fun i : Fin N => i.val < n)).card = n := by
-- proof
  apply NPartition.card_filter_fin_val_lt N n hn

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma sum_ite_fin_val_lt_eq
-- given
  (N n : ℕ)
  (hn : n ≤ N) :
-- imply
  (∑ i : Fin N, if i.val < n then 1 else 0) = n := by
-- proof
  apply NPartition.sum_ite_fin_val_lt_eq N n hn

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma colPartition_size
-- given
  (N n : ℕ)
  (hn : n ≤ N) :
-- imply
  (colPartition N n hn).size = n := by
-- proof
  apply NPartition.colPartition_size N n hn

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma colPartition_parts_lt
-- given
  (N n : ℕ)
  (i : Fin N)
  (hn : n ≤ N)
  (hi : i.val < n) :
-- imply
  (colPartition N n hn).parts i = 1 := by
-- proof
  apply NPartition.colPartition_parts_lt N n hn i hi

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma colPartition_parts_ge
-- given
  (N n : ℕ)
  (i : Fin N)
  (hn : n ≤ N)
  (hi : n ≤ i.val) :
-- imply
  (colPartition N n hn).parts i = 0 := by
-- proof
  apply NPartition.colPartition_parts_ge N n hn i hi

/--
[NPartition](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean)
-/
@[path]
private lemma zero_isTranspose
-- given
  {N : ℕ} :
-- imply
  IsTranspose (fun _ : Fin N => 0) (fun _ : Fin N => 0) := by
-- proof
  apply NPartition.zero_isTranspose


-- created on 2026-10-20
