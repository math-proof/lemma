import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.OrbitBasis
open Finset Finsupp MulAction Function Module OrbitBasis


/--
[rep_mem_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrbitBasis.lean)
-/
@[path]
private lemma rep_mem_orbit_eq
  {G : Type*}
  [Group G]
  {α : Type*}
  [Fintype α]
  [DecidableEq α]
  [MulAction G α]
  {O : orbitRel.Quotient G α} :
-- imply
  rep G α O ∈ orbitRel.Quotient.orbit O := by
-- proof
  apply OrbitBasis.rep_mem_orbit G α O

/--
[mk_rep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrbitBasis.lean)
-/
@[path]
private lemma mk_rep_eq
  {G : Type*}
  [Group G]
  {α : Type*}
  [Fintype α]
  [DecidableEq α]
  [MulAction G α]
  {O : orbitRel.Quotient G α} :
-- imply
  (Quotient.mk'' (rep G α O) : orbitRel.Quotient G α) = O := by
-- proof
  apply OrbitBasis.mk_rep G α O

/--
[invariant_iff_constant_on_orbits](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrbitBasis.lean)
-/
@[path]
private lemma invariant_iff_constant_on_orbits_eq
  {G : Type*}
  [Group G]
  {α : Type*}
  [Fintype α]
  [DecidableEq α]
  [MulAction G α]
  {G α}
  {v : α →₀ ℝ} :
-- imply
  v ∈ invariantSubspace G α ↔ ∀ a b : α, (Quotient.mk'' a : orbitRel.Quotient G α) = Quotient.mk'' b → v a = v b := by
-- proof
  apply OrbitBasis.invariant_iff_constant_on_orbits G α

/--
[orbitSum_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrbitBasis.lean)
-/
@[path]
private lemma orbitSum_apply_eq
  {G : Type*}
  [Group G]
  {α : Type*}
  [Fintype α]
  [DecidableEq α]
  [MulAction G α]
  {G α}
  {O : orbitRel.Quotient G α}
  {a : α} :
-- imply
  orbitSum O a = if a ∈ orbitRel.Quotient.orbit O then 1 else 0 := by
-- proof
  apply OrbitBasis.orbitSum_apply G α O a

/--
[orbitSum_mem_invariantSubspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrbitBasis.lean)
-/
@[path]
private lemma orbitSum_mem_invariantSubspace_eq
  {G : Type*}
  [Group G]
  {α : Type*}
  [Fintype α]
  [DecidableEq α]
  [MulAction G α]
  {G α}
  {O : orbitRel.Quotient G α} :
-- imply
  orbitSum O ∈ invariantSubspace G α := by
-- proof
  apply OrbitBasis.orbitSum_mem_invariantSubspace G α O

/--
[quotient_eq_of_mem_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrbitBasis.lean)
-/
@[path]
private lemma quotient_eq_of_mem_orbit_eq
  {G : Type*}
  [Group G]
  {α : Type*}
  [Fintype α]
  [DecidableEq α]
  [MulAction G α]
  {G α}
  {a : α}
  {O : orbitRel.Quotient G α}
-- given
  (h : a ∈ orbitRel.Quotient.orbit O) :
-- imply
  (Quotient.mk'' a : orbitRel.Quotient G α) = O := by
-- proof
  apply OrbitBasis.quotient_eq_of_mem_orbit G α h

/--
[sum_orbit_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrbitBasis.lean)
-/
@[path]
private lemma sum_orbit_indicator_eq
  {G : Type*}
  [Group G]
  {α : Type*}
  [Fintype α]
  [DecidableEq α]
  [MulAction G α]
  {G α}
  {c : orbitRel.Quotient G α → ℝ}
  {a : α}
  {O₀ : orbitRel.Quotient G α}
-- given
  (ha : a ∈ orbitRel.Quotient.orbit O₀) :
-- imply
  (∑ O : orbitRel.Quotient G α, c O * if a ∈ orbitRel.Quotient.orbit O then (1 : ℝ) else 0) = c O₀ := by
-- proof
  apply OrbitBasis.sum_orbit_indicator G α c a O₀ ha

/--
[orbitSum_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrbitBasis.lean)
-/
@[path]
private lemma orbitSum_linearIndependent_eq
  {G : Type*}
  [Group G]
  {α : Type*}
  [Fintype α]
  [DecidableEq α]
  [MulAction G α]
  {G α} :
-- imply
  LinearIndependent ℝ (fun O : orbitRel.Quotient G α => (⟨orbitSum O, orbitSum_mem_invariantSubspace O⟩ : ↥(invariantSubspace G α))) := by
-- proof
  apply OrbitBasis.orbitSum_linearIndependent G α

/--
[orbitSum_span](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrbitBasis.lean)
-/
@[path]
private lemma orbitSum_span_eq
  {G : Type*}
  [Group G]
  {α : Type*}
  [Fintype α]
  [DecidableEq α]
  [MulAction G α]
  {G α} :
-- imply
  ⊤ ≤ Submodule.span ℝ (Set.range (fun O : orbitRel.Quotient G α => (⟨orbitSum O, orbitSum_mem_invariantSubspace O⟩ : ↥(invariantSubspace G α)))) := by
-- proof
  apply OrbitBasis.orbitSum_span G α


-- created on 2026-10-23
