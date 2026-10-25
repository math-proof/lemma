import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc53harmbox.Part2
open Set SimpleGraph Finset StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls StatMech.Walls.Bc53Witness


/--
[bc53_canonicalArm_inbox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bc53_canonicalArm_inbox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a : Site d}
-- given
  (hx : x ∈ box d n)
  (hadj : (openSubgraph d ω).Adj x a) :
-- imply
  a ∈ box d (n + 1) := by
-- proof
  apply StatMech.Walls.bc53_canonicalArm_inbox hx hadj

/--
[bc53_canonicalArm_crosses_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bc53_canonicalArm_crosses_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a : Site d}
-- given
  (hax : a ≠ x)
  (habox : a ∈ box d (n + 1))
  (hinf : (cluster d (removeSite x ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d (n + 1), ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, x ∉ w.support := by
-- proof
  apply StatMech.Walls.bc53_canonicalArm_crosses_boundary ω n x a hax habox hinf

/--
[bc53_harmbox_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bc53_harmbox_succ_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d (n + 1) := by
-- proof
  apply StatMech.Walls.bc53_harmbox_succ ω n

/--
[threeRay_canonical_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma threeRay_canonical_origin_eq
  {d : ℕ} :
-- imply
  IsCanonicalTrifurcation 2 threeRayConfig (px 0) := by
-- proof
  apply StatMech.Walls.Bc53Witness.threeRay_canonical_origin

/--
[g_smul_px0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma g_smul_px0_eq
  {d : ℕ} :
-- imply
  (g • px 0) = (![(1 : ℤ), 0] : Site 2) := by
-- proof
  apply StatMech.Walls.Bc53Witness.g_smul_px0

/--
[g_smul_px1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma g_smul_px1_eq
  {d : ℕ} :
-- imply
  (g • px 1) = (![(2 : ℤ), 0] : Site 2) := by
-- proof
  apply StatMech.Walls.Bc53Witness.g_smul_px1

/--
[bwall_isTrifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bwall_isTrifurcation_eq
  {d : ℕ} :
-- imply
  IsTrifurcation 2 bwallConfig (![(1 : ℤ), 0] : Site 2) := by
-- proof
  apply StatMech.Walls.Bc53Witness.bwall_isTrifurcation

/--
[bwall_hub_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bwall_hub_in_box_eq
  {d : ℕ} :
-- imply
  (![(1 : ℤ), 0] : Site 2) ∈ box 2 1 := by
-- proof
  apply StatMech.Walls.Bc53Witness.bwall_hub_in_box

/--
[bwall_arm_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bwall_arm_adj_eq
  {d : ℕ} :
-- imply
  (openSubgraph 2 bwallConfig).Adj (![(1 : ℤ), 0] : Site 2) (![(2 : ℤ), 0] : Site 2) := by
-- proof
  apply StatMech.Walls.Bc53Witness.bwall_arm_adj

/--
[bwall_arm_cut_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bwall_arm_cut_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 (removeSite (![(1 : ℤ), 0] : Site 2) bwallConfig) (![(2 : ℤ), 0] : Site 2)).Infinite := by
-- proof
  apply StatMech.Walls.Bc53Witness.bwall_arm_cut_infinite

/--
[bwall_arm_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bwall_arm_outside_box_eq
  {d : ℕ} :
-- imply
  (![(2 : ℤ), 0] : Site 2) ∉ box 2 1 := by
-- proof
  apply StatMech.Walls.Bc53Witness.bwall_arm_outside_box

/--
[bc53_harmbox_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bc53_harmbox_false_eq
  {d : ℕ} :
-- imply
  ¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), ∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) := by
-- proof
  apply StatMech.Walls.bc53_harmbox_false

/--
[bc53_harmbox_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bc53_harmbox_of_interior_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hint : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x ∈ box d (n - 1)) :
-- imply
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n := by
-- proof
  apply StatMech.Walls.bc53_harmbox_of_interior ω n hn hint

/--
[bc53_count_of_harmbox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bc53_count_of_harmbox_eq
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
  apply StatMech.Walls.bc53_count_of_harmbox ω n hn hcanon harmbox

/--
[bc53_count_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bc53_count_of_interior_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
  (hint : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x ∈ box d (n - 1)) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc53_count_of_interior ω n hn hcanon hint

/--
[bc53_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean)
-/
@[path]
private lemma bc53_status_eq
  {d : ℕ} :
-- imply
  (¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), ∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d (n + 1)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → (∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) → (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) → Tcount d ω n ≤ boxSV_boundaryCard d n) := by
-- proof
  apply StatMech.Walls.bc53_status


-- created on 2026-10-23
