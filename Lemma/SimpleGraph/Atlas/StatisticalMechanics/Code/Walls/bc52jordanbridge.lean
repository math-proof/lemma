import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc52jordanbridge.Part2
open Set SimpleGraph Finset StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls StatMech.Walls.Bc52Witness


/--
[bc52_spanForest_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc52jordanbridge.lean)
-/
@[path]
private lemma bc52_spanForest_acyclic_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  (osf_spanForest G).IsAcyclic := by
-- proof
  apply StatMech.Walls.bc52_spanForest_acyclic G

/--
[bc52_subgraph_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc52jordanbridge.lean)
-/
@[path]
private lemma bc52_subgraph_acyclic_eq
  {d : ℕ}
  [Fintype V]
  {G T : SimpleGraph V}
-- given
  (hsub : T ≤ osf_spanForest G) :
-- imply
  T.IsAcyclic := by
-- proof
  apply StatMech.Walls.bc52_subgraph_acyclic G T hsub

/--
[thetaG_not_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc52jordanbridge.lean)
-/
@[path]
private lemma thetaG_not_acyclic_eq
  {d : ℕ} :
-- imply
  ¬ thetaG.IsAcyclic := by
-- proof
  apply StatMech.Walls.Bc52Witness.thetaG_not_acyclic

/--
[thetaG_spanForest_subgraph_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc52jordanbridge.lean)
-/
@[path]
private lemma thetaG_spanForest_subgraph_acyclic_eq
  {d : ℕ}
  {H : SimpleGraph (Fin 4)}
-- given
  (hsub : H ≤ osf_spanForest thetaG) :
-- imply
  H.IsAcyclic := by
-- proof
  apply StatMech.Walls.Bc52Witness.thetaG_spanForest_subgraph_acyclic hsub

/--
[bc52_acyclic_no_boundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc52jordanbridge.lean)
-/
@[path]
private lemma bc52_acyclic_no_boundedRegion_eq
  {d : ℕ}
  {P : Lattice.PlanarZ2Subgraph}
-- given
  (hac : P.G.IsAcyclic) :
-- imply
  IsEmpty {c : (Lattice.whb_faceRegion (Lattice.imageGraph P)).ConnectedComponent // c.supp.Finite} := by
-- proof
  apply StatMech.Walls.bc52_acyclic_no_boundedRegion P hac

/--
[bc52_boundedRegion_forces_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc52jordanbridge.lean)
-/
@[path]
private lemma bc52_boundedRegion_forces_cycle_eq
  {d : ℕ}
  {P : Lattice.PlanarZ2Subgraph}
-- given
  (hne : Nonempty {c : (Lattice.whb_faceRegion (Lattice.imageGraph P)).ConnectedComponent // c.supp.Finite}) :
-- imply
  ¬ P.G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bc52_boundedRegion_forces_cycle P hne

/--
[bc52_globalArmForest_of_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc52jordanbridge.lean)
-/
@[path]
private lemma bc52_globalArmForest_of_canonical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
  (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n)
  (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
-- imply
  bc51_GlobalArmForest ω n := by
-- proof
  apply StatMech.Walls.bc52_globalArmForest_of_canonical ω n hn hcanon harmbox hexists

/--
[bc52_Tcount_le_boundary_of_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc52jordanbridge.lean)
-/
@[path]
private lemma bc52_Tcount_le_boundary_of_canonical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
  (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc52_Tcount_le_boundary_of_canonical ω n hn hcanon harmbox

/--
[bc52_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc52jordanbridge.lean)
-/
@[path]
private lemma bc52_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (osf_spanForest G).IsAcyclic) ∧ (¬ Bc52Witness.thetaG.IsAcyclic) ∧ (∀ (P : Lattice.PlanarZ2Subgraph), P.G.IsAcyclic → IsEmpty {c : (Lattice.whb_faceRegion (Lattice.imageGraph P)).ConnectedComponent // c.supp.Finite}) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → (∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) → (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) → (∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) → bc51_GlobalArmForest ω n) := by
-- proof
  apply StatMech.Walls.bc52_status


-- created on 2026-10-23
