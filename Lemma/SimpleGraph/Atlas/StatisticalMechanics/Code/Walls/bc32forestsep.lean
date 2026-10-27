import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc32forestsep.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc32_not_tfree_of_branchTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_not_tfree_of_branchTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ a aⱼ y : Site d}
-- given
  (hmeet : Connected d (removeSite x₀ ω) a aⱼ)
  (hyj : Connected d (removeSite x₀ ω) aⱼ y)
  (hyT : y ∈ tfc_trifFinset ω n) :
-- imply
  ¬ (∀ z, Connected d (removeSite x₀ ω) a z → z ∉ tfc_trifFinset ω n) := by
-- proof
  apply StatMech.Walls.bc32_not_tfree_of_branchTrif ω n hmeet hyj hyT

/--
[bc32_no_tfreeArm_of_armTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_no_tfreeArm_of_armTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ a₁ a₂ a₃ : Site d}
  {y : Fin 3 → Site d}
  {a : Site d}
-- given
  (htrifArm : ∀ i, y i ∈ tfc_trifFinset ω n ∧ Connected d (removeSite x₀ ω) (![a₁, a₂, a₃] i) (y i))
  (hcover : Connected d (removeSite x₀ ω) a a₁ ∨ Connected d (removeSite x₀ ω) a a₂ ∨ Connected d (removeSite x₀ ω) a a₃) :
-- imply
  ¬ (∀ z, Connected d (removeSite x₀ ω) a z → z ∉ tfc_trifFinset ω n) := by
-- proof
  apply StatMech.Walls.bc32_no_tfreeArm_of_armTrif ω n y htrifArm hcover

/--
[bc32_not_tfreeDownArmData_of_clawTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_not_tfreeDownArmData_of_clawTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
  {x₀ a₁ a₂ a₃ : Site d}
  {y : Fin 3 → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (htrifArm : ∀ i, y i ∈ tfc_trifFinset ω n ∧ Connected d (removeSite x₀ ω) (![a₁, a₂, a₃] i) (y i))
  (hcover : ∀ a : Site d, (cluster d (removeSite x₀ ω) a).Infinite → Connected d ω x₀ a → Connected d (removeSite x₀ ω) a a₁ ∨ Connected d (removeSite x₀ ω) a a₂ ∨ Connected d (removeSite x₀ ω) a a₃) :
-- imply
  ¬ bc31_TfreeDownArmData ω n rank := by
-- proof
  apply StatMech.Walls.bc32_not_tfreeDownArmData_of_clawTrif ω n rank y hx0box htri0 htrifArm hcover

/--
[bc32_escapingRay_of_tfree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_escapingRay_of_tfree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a : Site d}
-- given
  (hinf : (cluster d (removeSite x ω) a).Infinite)
  (hTfree : ∀ z, Connected d (removeSite x ω) a z → z ∉ tfc_trifFinset ω n) :
-- imply
  ∀ m : ℕ, ∃ z, z ∉ box d m ∧ ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n := by
-- proof
  apply StatMech.Walls.bc32_escapingRay_of_tfree ω n hinf hTfree

/--
[bc32_escapingDownArmData_of_tfreeDownArmData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_escapingDownArmData_of_tfreeDownArmData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (h : bc31_TfreeDownArmData ω n rank) :
-- imply
  bc32_EscapingDownArmData ω n rank := by
-- proof
  apply StatMech.Walls.bc32_escapingDownArmData_of_tfreeDownArmData ω n rank h

/--
[bc32_globalCutDownArmData_of_escapingDownArmData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_globalCutDownArmData_of_escapingDownArmData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (h : bc32_EscapingDownArmData ω n rank) :
-- imply
  bc30_GlobalCutDownArmData ω n rank := by
-- proof
  apply StatMech.Walls.bc32_globalCutDownArmData_of_escapingDownArmData ω n rank h

/--
[bc32_bundledRootedDownArmForest_of_escapingDownArmData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_bundledRootedDownArmForest_of_escapingDownArmData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y)
  (h : bc32_EscapingDownArmData ω n rank) :
-- imply
  bc29_BundledRootedDownArmForest ω n := by
-- proof
  apply StatMech.Walls.bc32_bundledRootedDownArmForest_of_escapingDownArmData ω n rank hinj h

/--
[bc32_Tcount_le_boundary_of_escapingDownArmData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_Tcount_le_boundary_of_escapingDownArmData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hn : 1 ≤ n)
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y)
  (h : bc32_EscapingDownArmData ω n rank) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc32_Tcount_le_boundary_of_escapingDownArmData ω n hn rank hinj h

/--
[bc32_escapingDownArmData_of_threeChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_escapingDownArmData_of_threeChain_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ m g : Site d}
  {b : Site d → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (hmbox : m ∈ box d n)
  (hgbox : g ∈ box d n)
  (hx0m : x₀ ≠ m)
  (hx0g : x₀ ≠ g)
  (hmg : m ≠ g)
  (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (∀ mm : ℕ, ∃ z, z ∉ box d mm ∧ ∃ w : (openSubgraph d (removeSite x₀ ω)).Walk (b x₀) z, ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n))
  (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧ (∀ mm : ℕ, ∃ z, z ∉ box d mm ∧ ∃ w : (openSubgraph d (removeSite m ω)).Walk (b m) z, ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n))
  (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧ (∀ mm : ℕ, ∃ z, z ∉ box d mm ∧ ∃ w : (openSubgraph d (removeSite g ω)).Walk (b g) z, ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n))
  (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
  (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
  (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
-- imply
  bc32_EscapingDownArmData ω n (fun z => if z = x₀ then toLex (0, 0) else if z = m then toLex (1, 0) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc32_escapingDownArmData_of_threeChain ω n b hx0box hmbox hgbox hx0m hx0g hmg hthree hbx0 hbm hbg hsxm hsxg hsmg

/--
[bc32_escapingDownArmData_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_escapingDownArmData_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
  {b : Site d → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (hydata : ∀ i, y i ∈ box d n ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
  (hyinj : Function.Injective y)
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (∀ mm : ℕ, ∃ z, z ∉ box d mm ∧ ∃ w : (openSubgraph d (removeSite x₀ ω)).Walk (b x₀) z, ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n))
  (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧ (∀ mm : ℕ, ∃ z, z ∉ box d mm ∧ ∃ w : (openSubgraph d (removeSite (y i) ω)).Walk (b (y i)) z, ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n))
  (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
  (hssib : ∀ i j : Fin 3, (j : ℕ) < i → ¬ Connected d (removeSite (y i) ω) (b (y i)) (b (y j))) :
-- imply
  bc32_EscapingDownArmData ω n (fun z => if z = x₀ then toLex (0, 0) else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc32_escapingDownArmData_of_claw ω n x₀ y b hx0box hydata hyinj hsingle hbx0 hby hsx0 hssib

/--
[bc32_pos_edge_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_pos_edge_open_eq
  {d : ℕ}
  {k : ℤ}
-- given
  (hk : 1 ≤ k) :
-- imply
  (openSubgraph 2 (removeSite (arc_p (-2)) arc_rayConfig)).Adj (arc_p k) (arc_p (k+1)) := by
-- proof
  apply StatMech.Walls.bc32_pos_edge_open k hk

/--
[bc32_pos_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_pos_walk_eq
  {d : ℕ}
  {j : ℕ} :
-- imply
  ∃ w : (openSubgraph 2 (removeSite (arc_p (-2)) arc_rayConfig)).Walk (arc_p 1) (arc_p (1 + (j:ℤ))), ∀ v ∈ w.support, ∃ k : ℤ, 1 ≤ k ∧ v = arc_p k := by
-- proof
  apply StatMech.Walls.bc32_pos_walk j

/--
[bc32_arc_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_arc_outside_eq
  {d : ℕ}
  {j : ℕ} :
-- imply
  arc_p (1 + (j:ℤ)) ∉ box 2 j := by
-- proof
  apply StatMech.Walls.bc32_arc_outside j

/--
[bc32_escapingClause_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean)
-/
@[path]
private lemma bc32_escapingClause_nonvacuous_eq
  {d : ℕ} :
-- imply
  ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x a : Site 2) (T : Finset (Site 2)), a ∉ T ∧ x ∈ T ∧ (∀ m : ℕ, ∃ z, z ∉ box 2 m ∧ ∃ w : (openSubgraph 2 (removeSite x ω)).Walk a z, ∀ v ∈ w.support, v ∉ T) := by
-- proof
  apply StatMech.Walls.bc32_escapingClause_nonvacuous


-- created on 2026-10-23
