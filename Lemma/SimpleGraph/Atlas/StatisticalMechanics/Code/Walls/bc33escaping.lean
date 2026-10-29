import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc33escaping.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc33_rayWalk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean)
-/
@[path]
private lemma bc33_rayWalk_support_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {r : ℕ → V}
  {j : ℕ}
-- given
  (hadj : ∀ k, G.Adj (r k) (r (k + 1))) :
-- imply
  ∀ v ∈ (bc33_rayWalk G r hadj j).support, ∃ k ≤ j, v = r k := by
-- proof
  apply StatMech.Walls.bc33_rayWalk_support G r hadj j

/--
[bc33_injRay_escapes_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean)
-/
@[path]
private lemma bc33_injRay_escapes_box_eq
  {d : ℕ}
  {r : ℕ → Site d}
  {m : ℕ}
-- given
  (hinj : Function.Injective r) :
-- imply
  ∃ j, r j ∉ box d m := by
-- proof
  apply StatMech.Walls.bc33_injRay_escapes_box r hinj m

/--
[bc33_escapingWalks_of_TavoidingRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean)
-/
@[path]
private lemma bc33_escapingWalks_of_TavoidingRay_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a : Site d}
  {r : ℕ → Site d}
-- given
  (hr0 : r 0 = a)
  (hinj : Function.Injective r)
  (hadj : ∀ k, (openSubgraph d (removeSite x ω)).Adj (r k) (r (k + 1)))
  (hT : ∀ k, r k ∉ tfc_trifFinset ω n) :
-- imply
  ∀ m : ℕ, ∃ z, z ∉ box d m ∧ ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, ∀ v ∈ w.support, v ∉ tfc_trifFinset ω n := by
-- proof
  apply StatMech.Walls.bc33_escapingWalks_of_TavoidingRay ω n r hr0 hinj hadj hT

/--
[bc33_escapingDownArmData_of_TavoidingRayData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean)
-/
@[path]
private lemma bc33_escapingDownArmData_of_TavoidingRayData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (h : bc33_TavoidingRayData ω n rank) :
-- imply
  bc32_EscapingDownArmData ω n rank := by
-- proof
  apply StatMech.Walls.bc33_escapingDownArmData_of_TavoidingRayData ω n rank h

/--
[bc33_globalCutDownArmData_of_TavoidingRayData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean)
-/
@[path]
private lemma bc33_globalCutDownArmData_of_TavoidingRayData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (h : bc33_TavoidingRayData ω n rank) :
-- imply
  bc30_GlobalCutDownArmData ω n rank := by
-- proof
  apply StatMech.Walls.bc33_globalCutDownArmData_of_TavoidingRayData ω n rank h

/--
[bc33_bundledRootedDownArmForest_of_TavoidingRayData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean)
-/
@[path]
private lemma bc33_bundledRootedDownArmForest_of_TavoidingRayData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y)
  (h : bc33_TavoidingRayData ω n rank) :
-- imply
  bc29_BundledRootedDownArmForest ω n := by
-- proof
  apply StatMech.Walls.bc33_bundledRootedDownArmForest_of_TavoidingRayData ω n rank hinj h

/--
[bc33_Tcount_le_boundary_of_TavoidingRayData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean)
-/
@[path]
private lemma bc33_Tcount_le_boundary_of_TavoidingRayData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hn : 1 ≤ n)
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y)
  (h : bc33_TavoidingRayData ω n rank) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc33_Tcount_le_boundary_of_TavoidingRayData ω n hn rank hinj h

/--
[bc33_burton_keane_bernoulli_of_TavoidingRayData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean)
-/
@[path]
private lemma bc33_burton_keane_bernoulli_of_TavoidingRayData_eq
  {d : ℕ}
  {rank : ConfigSpace (Sym2 (Site d)) → ℕ → Site d → ℕ ×ₗ ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank ω n x ≠ rank ω n y)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc33_TavoidingRayData ω n (rank ω n))
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc33_burton_keane_bernoulli_of_TavoidingRayData hd p hp1 hp0 rank hinj hres htrif

/--
[bc33_TavoidingRayData_of_threeChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean)
-/
@[path]
private lemma bc33_TavoidingRayData_of_threeChain_eq
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
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ ∃ r : ℕ → Site d, r 0 = b x₀ ∧ Function.Injective r ∧ (∀ k, (openSubgraph d (removeSite x₀ ω)).Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ tfc_trifFinset ω n))
  (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧ ∃ r : ℕ → Site d, r 0 = b m ∧ Function.Injective r ∧ (∀ k, (openSubgraph d (removeSite m ω)).Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ tfc_trifFinset ω n))
  (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧ ∃ r : ℕ → Site d, r 0 = b g ∧ Function.Injective r ∧ (∀ k, (openSubgraph d (removeSite g ω)).Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ tfc_trifFinset ω n))
  (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
  (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
  (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
-- imply
  bc33_TavoidingRayData ω n (fun z => if z = x₀ then toLex (0, 0) else if z = m then toLex (1, 0) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc33_TavoidingRayData_of_threeChain ω n b hx0box hmbox hgbox hx0m hx0g hmg hthree hbx0 hbm hbg hsxm hsxg hsmg

/--
[bc33_TavoidingRayData_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean)
-/
@[path]
private lemma bc33_TavoidingRayData_of_claw_eq
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
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ ∃ r : ℕ → Site d, r 0 = b x₀ ∧ Function.Injective r ∧ (∀ k, (openSubgraph d (removeSite x₀ ω)).Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ tfc_trifFinset ω n))
  (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧ ∃ r : ℕ → Site d, r 0 = b (y i) ∧ Function.Injective r ∧ (∀ k, (openSubgraph d (removeSite (y i) ω)).Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ tfc_trifFinset ω n))
  (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
  (hssib : ∀ i j : Fin 3, (j : ℕ) < i → ¬ Connected d (removeSite (y i) ω) (b (y i)) (b (y j))) :
-- imply
  bc33_TavoidingRayData ω n (fun z => if z = x₀ then toLex (0, 0) else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc33_TavoidingRayData_of_claw ω n x₀ y b hx0box hydata hyinj hsingle hbx0 hby hsx0 hssib

/--
[bc33_arc_ray](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean)
-/
@[path]
private lemma bc33_arc_ray_eq
  {d : ℕ} :
-- imply
  (fun k : ℕ => arc_p (1 + (k : ℤ))) 0 = arc_p 1 ∧ Function.Injective (fun k : ℕ => arc_p (1 + (k : ℤ))) ∧ (∀ k : ℕ, (openSubgraph 2 (removeSite (arc_p (-2)) arc_rayConfig)).Adj (arc_p (1 + (k : ℤ))) (arc_p (1 + ((k + 1 : ℕ) : ℤ)))) := by
-- proof
  apply StatMech.Walls.bc33_arc_ray

/--
[bc33_TavoidingRay_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean)
-/
@[path]
private lemma bc33_TavoidingRay_nonvacuous_eq
  {d : ℕ} :
-- imply
  ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x a : Site 2) (T : Finset (Site 2)), a ∉ T ∧ x ∈ T ∧ ∃ r : ℕ → Site 2, r 0 = a ∧ Function.Injective r ∧ (∀ k, (openSubgraph 2 (removeSite x ω)).Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ T) := by
-- proof
  apply StatMech.Walls.bc33_TavoidingRay_nonvacuous


-- created on 2026-10-23
