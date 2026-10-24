import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bfcforestacyclic
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bfc_acyclic_of_walkInjHom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfcforestacyclic.lean)
-/
@[path]
private lemma bfc_acyclic_of_walkInjHom_eq
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {f : G →g H}
-- given
  (hH : H.IsAcyclic)
  (hinj : ∀ {v : V} (c : G.Walk v v), c.IsCycle → Set.InjOn f {x | x ∈ c.support}) :
-- imply
  G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bfc_acyclic_of_walkInjHom f hH hinj

/--
[bfc_disjointStar_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfcforestacyclic.lean)
-/
@[path]
private lemma bfc_disjointStar_acyclic_eq
  {β : Type} :
-- imply
  (bc64_starForest β).IsAcyclic := by
-- proof
  apply StatMech.Walls.bfc_disjointStar_acyclic β

/--
[bfc_disjointStar_leaves_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfcforestacyclic.lean)
-/
@[path]
private lemma bfc_disjointStar_leaves_interior_eq
  {R : ℕ}
-- given
  (hd : 1 ≤ d)
  (hR : 2 ≤ R) :
-- imply
  bc112_leaf hd (0 : Site d) 1 ∉ vertexBoundary d R := by
-- proof
  apply StatMech.Walls.bfc_disjointStar_leaves_interior hd hR

/--
[bfc_gap1_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfcforestacyclic.lean)
-/
@[path]
private lemma bfc_gap1_free_eq
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L) :
-- imply
  bc112_SeparatedArmGraph ω L R := by
-- proof
  apply StatMech.Walls.bfc_gap1_free hd ω L R hL

/--
[bfc_bc69_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfcforestacyclic.lean)
-/
@[path]
private lemma bfc_bc69_nonvacuous_eq
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bfc_bc69_nonvacuous ω L R hz₀ hz₁ hzne hno

/--
[bfc_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfcforestacyclic.lean)
-/
@[path]
private lemma bfc_status_eq
-- given
  (hd : 1 ≤ d) :
-- imply
  (∀ (β : Type), (bc64_starForest β).IsAcyclic) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 3 ≤ L → bc112_SeparatedArmGraph ω L R) ∧ (∀ {R : ℕ}, 2 ≤ R → bc112_leaf hd (0 : Site d) 1 ∉ vertexBoundary d R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) → bc69_Gn_globalForest ω L R) := by
-- proof
  apply StatMech.Walls.bfc_status hd


-- created on 2026-10-23
