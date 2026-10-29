import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc40funnel.Part4
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc40_funnel_demands_all_sites_reach_s](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_funnel_demands_all_sites_reach_s_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {t s : Site d}
-- given
  (hgeo : bc39_ArmCutGeometryFixed ω n)
  (htbox : t ∈ box d n)
  (htri : IsTrifurcation d ω t)
  (hadj : bc37_ArmAdjacent ω n t s) :
-- imply
  ∃ b : Site d → Site d, ∀ x, x ≠ s → x ≠ t → Connected d (removeSite t ω) (b x) s := by
-- proof
  apply StatMech.Walls.bc40_funnel_demands_all_sites_reach_s ω n hgeo htbox htri hadj

/--
[bc40_armCutGeometryFixed_false_of_idempotentDownArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_armCutGeometryFixed_false_of_idempotentDownArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {t s : Site d}
-- given
  (htbox : t ∈ box d n)
  (htri : IsTrifurcation d ω t)
  (hadj : bc37_ArmAdjacent ω n t s)
  (hidem : ∀ b : Site d → Site d, (∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) → b (b t) = b t ∧ b t ≠ s ∧ b t ≠ t) :
-- imply
  ¬ bc39_ArmCutGeometryFixed ω n := by
-- proof
  apply StatMech.Walls.bc40_armCutGeometryFixed_false_of_idempotentDownArm ω n htbox htri hadj hidem

/--
[bc40_armRealisation_of_cutGeometryFixed'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_armRealisation_of_cutGeometryFixed'_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc40_ArmCutGeometryFixed' ω n)
  (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc40_RootSideComparable ω n rank par) :
-- imply
  bc38_ArmRealisation ω n := by
-- proof
  apply StatMech.Walls.bc40_armRealisation_of_cutGeometryFixed' ω n hgeo hroot_side

/--
[bc40_parentFunneling_of_cutGeometryFixed'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_parentFunneling_of_cutGeometryFixed'_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc40_ArmCutGeometryFixed' ω n)
  (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc40_RootSideComparable ω n rank par) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc40_parentFunneling_of_cutGeometryFixed' ω n hgeo hroot_side

/--
[bc40_selfDownArm_of_cutGeometryFixed'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_selfDownArm_of_cutGeometryFixed'_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc40_ArmCutGeometryFixed' ω n)
  (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc40_RootSideComparable ω n rank par) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc40_selfDownArm_of_cutGeometryFixed' ω n hgeo hroot_side

/--
[bc40_Tcount_le_boundary_of_cutGeometryFixed'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_Tcount_le_boundary_of_cutGeometryFixed'_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hgeo : bc40_ArmCutGeometryFixed' ω n)
  (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc40_RootSideComparable ω n rank par) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc40_Tcount_le_boundary_of_cutGeometryFixed' ω n hn hgeo hroot_side

/--
[bc40_burton_keane_bernoulli_of_cutGeometryFixed'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_burton_keane_bernoulli_of_cutGeometryFixed'_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n)
  (hroot_side : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc40_RootSideComparable ω n rank par)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc40_burton_keane_bernoulli_of_cutGeometryFixed' hd p hp1 hp0 hgeo hroot_side htrif

/--
[bc40_armCutGeometryFixed'_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_armCutGeometryFixed'_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc40_ArmCutGeometryFixed' ω n := by
-- proof
  apply StatMech.Walls.bc40_armCutGeometryFixed'_of_noTrif ω n hno

/--
[bc40_armCutGeometryFixed'_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_armCutGeometryFixed'_of_twoTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
  {b : Site d → Site d}
-- given
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
  (hloc_x : ∀ s, bc37_ArmAdjacent ω n x₀ s → ¬ Connected d (removeSite x₀ ω) (b x₀) (b s))
  (hself_x : ∀ s, bc37_ArmAdjacent ω n x₀ s → ¬ Connected d (removeSite x₀ ω) (b x₀) s)
  (hloc_y : ∀ s, bc37_ArmAdjacent ω n y₀ s → ¬ Connected d (removeSite y₀ ω) (b y₀) (b s))
  (hself_y : ∀ s, bc37_ArmAdjacent ω n y₀ s → ¬ Connected d (removeSite y₀ ω) (b y₀) s)
  (hfun_x : ∀ s, bc37_ArmAdjacent ω n x₀ s → ∀ x, x ≠ x₀ → Connected d (removeSite x₀ ω) x s → Connected d (removeSite x₀ ω) (b x) s)
  (hfun_y : ∀ s, bc37_ArmAdjacent ω n y₀ s → ∀ x, x ≠ y₀ → Connected d (removeSite y₀ ω) x s → Connected d (removeSite y₀ ω) (b x) s) :
-- imply
  bc40_ArmCutGeometryFixed' ω n := by
-- proof
  apply StatMech.Walls.bc40_armCutGeometryFixed'_of_twoTrif ω n b htwo hbx0 hby0 hloc_x hself_x hloc_y hself_y hfun_x hfun_y

/--
[bc40_armCutGeometryFixed'_of_threeChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_armCutGeometryFixed'_of_threeChain_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ m g : Site d}
  {b : Site d → Site d}
-- given
  (hx0m : x₀ ≠ m)
  (hx0g : x₀ ≠ g)
  (hmg : m ≠ g)
  (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
  (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
  (hloc : ∀ t s, (t = x₀ ∨ t = m ∨ t = g) → bc37_ArmAdjacent ω n t s → ¬ Connected d (removeSite t ω) (b t) (b s))
  (hself : ∀ t s, (t = x₀ ∨ t = m ∨ t = g) → bc37_ArmAdjacent ω n t s → ¬ Connected d (removeSite t ω) (b t) s)
  (hfun : ∀ t s, (t = x₀ ∨ t = m ∨ t = g) → bc37_ArmAdjacent ω n t s → ∀ x, x ≠ t → Connected d (removeSite t ω) x s → Connected d (removeSite t ω) (b x) s) :
-- imply
  bc40_ArmCutGeometryFixed' ω n := by
-- proof
  apply StatMech.Walls.bc40_armCutGeometryFixed'_of_threeChain ω n b hx0m hx0g hmg hthree hbx0 hbm hbg hloc hself hfun

/--
[bc40_chainShadow_universalFunnel_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_chainShadow_universalFunnel_false_eq
  {d : ℕ} :
-- imply
  ¬ ∀ (b : Fin 6 → Fin 6), b = ![3, 4, 5, 3, 4, 5] → ∀ t s : Fin 6, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨ (t = 2 ∧ s = 1) → ∀ x : Fin 6, x ≠ s → x ≠ t → bc40_chainLab t (b x) = bc40_chainLab t s := by
-- proof
  apply StatMech.Walls.bc40_chainShadow_universalFunnel_false

/--
[bc40_chainShadow_allTrifFunnel_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_chainShadow_allTrifFunnel_false_eq
  {d : ℕ} :
-- imply
  ¬ ∀ (b : Fin 6 → Fin 6), b = ![3, 4, 5, 3, 4, 5] → ∀ t s : Fin 6, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨ (t = 2 ∧ s = 1) → ∀ x : Fin 6, (x = 0 ∨ x = 1 ∨ x = 2) → x ≠ s → x ≠ t → bc40_chainLab t (b x) = bc40_chainLab t s := by
-- proof
  apply StatMech.Walls.bc40_chainShadow_allTrifFunnel_false

/--
[bc40_chainShadow_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_chainShadow_consistent_eq
  {d : ℕ} :
-- imply
  ∃ (b : Fin 6 → Fin 6) (Rc : Fin 6 → Fin 6 → Fin 6 → Prop), (∀ c u v, Rc c u v ↔ bc40_chainLab c u = bc40_chainLab c v) ∧ (∀ t s : Fin 6, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨ (t = 2 ∧ s = 1) → (¬ Rc t (b t) (b s)) ∧ (¬ Rc t (b t) s) ∧ (∀ x : Fin 6, x ≠ t → Rc t x s → Rc t (b x) s)) := by
-- proof
  apply StatMech.Walls.bc40_chainShadow_consistent

/--
[bc40_rootSideComparable_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_rootSideComparable_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
  {par : Site d → Site d}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc40_RootSideComparable ω n rank par := by
-- proof
  apply StatMech.Walls.bc40_rootSideComparable_of_noTrif ω n rank par hno

/--
[bc40_rootSideComparable_chain_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean)
-/
@[path]
private lemma bc40_rootSideComparable_chain_consistent_eq
  {d : ℕ} :
-- imply
  ∃ (rank : Fin 3 → ℕ) (par : Fin 3 → Fin 3) (R : Fin 3 → Fin 3 → Fin 3 → Prop), (∀ c u v, R c u v ↔ bc40_chainSiteLab c u = bc40_chainSiteLab c v) ∧ rank 0 < rank 1 ∧ rank 1 < rank 2 ∧ par 1 = 0 ∧ par 2 = 1 ∧ (∀ x y : Fin 3, rank x < rank y → x ≠ par y → R y x (par y)) := by
-- proof
  apply StatMech.Walls.bc40_rootSideComparable_chain_consistent


-- created on 2026-10-23
