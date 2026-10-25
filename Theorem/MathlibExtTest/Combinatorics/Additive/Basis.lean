/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Additive/Basis.lean -/


import Def.Combinatorics.Additive.Basis
open Set Filter
open scoped Pointwise


-- Normal API use: the basis predicates accept a set and order.
noncomputable example (A : Set ℕ) (n : ℕ) : Prop :=
  A.IsAsymptoticAddBasisOfOrder n

noncomputable example (A : Set ℕ) (n : ℕ) : Prop :=
  A.IsAddBasisOfOrder n

noncomputable example (A : Set ℕ) : Prop :=
  A.IsAsymptoticAddBasis

noncomputable example (A : Set ℕ) (n : ℕ) : Prop :=
  A.IsWeakAddBasisOfOrder n

noncomputable example (A : Set ℕ) : Prop :=
  A.IsWeakAddBasis

-- Semantic check: an exact basis is a weak basis of the same order.
example (A : Set ℕ) (n : ℕ) (h : A.IsAddBasisOfOrder n) :
    A.IsWeakAddBasisOfOrder n := by
  intro a
  exact ⟨n, le_rfl, h a⟩

-- Semantic check: `Set.univ` is an exact (hence weak) basis of order 1.
example : (Set.univ : Set ℕ).IsAddBasisOfOrder 1 := by
  intro a
  simp only [one_nsmul, Set.mem_univ]

