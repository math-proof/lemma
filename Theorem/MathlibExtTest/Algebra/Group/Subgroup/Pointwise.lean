/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Group/Subgroup/Pointwise.lean -/


import Lemma.Set.Closure.eq.N.of.Eq
import Mathlib.Algebra.Group.Pointwise.Set.Basic
open scoped Pointwise


-- exponent zero: {1} is inverse-closed and its closure is the union of its powers
example {G : Type*} [Group G] :
    (Subgroup.closure ({1} : Set G) : Set G) = ⋃ n : ℕ, ({1} : Set G) ^ n :=
  Subgroup.closure_eq_iUnion_pow (by simp)

-- exponent zero membership: 1 lies in the union via n = 0
example {G : Type*} [Group G] :
    (1 : G) ∈ (⋃ n : ℕ, ({1} : Set G) ^ n) :=
  Set.mem_iUnion.mpr ⟨0, by simp⟩

-- nontrivial inverse-closed subset {a, a⁻¹} is inverse-closed by simp
example {G : Type*} [Group G] (a : G) :
    (({a, a⁻¹} : Set G)⁻¹ = {a, a⁻¹}) := by
  ext x
  simp
  exact Or.comm

-- closure of the nontrivial inverse-closed set equals the union of its powers
example {G : Type*} [Group G] (a : G) :
    (Subgroup.closure ({a, a⁻¹} : Set G) : Set G) =
      ⋃ n : ℕ, ({a, a⁻¹} : Set G) ^ n :=
  Subgroup.closure_eq_iUnion_pow (by
    ext x
    simp
    exact Or.comm)

-- combined check that the theorem applies to both the trivial and nontrivial cases
example {G : Type*} [Group G] (a : G) :
    (Subgroup.closure ({1} : Set G) : Set G) = ⋃ n : ℕ, ({1} : Set G) ^ n ∧
    (Subgroup.closure ({a, a⁻¹} : Set G) : Set G) = ⋃ n : ℕ, ({a, a⁻¹} : Set G) ^ n :=
  ⟨Subgroup.closure_eq_iUnion_pow (by simp), Subgroup.closure_eq_iUnion_pow (by ext x; simp; exact Or.comm)⟩

