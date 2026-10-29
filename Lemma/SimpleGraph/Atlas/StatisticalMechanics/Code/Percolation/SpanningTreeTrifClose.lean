import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[stt_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_reachable_iff_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (a b : {x : Site d // x ∈ tfc_trifFinset ω n}) :
-- imply
  (stt_trifGraph ω n).Reachable a b ↔ Connected d ω a.1 b.1 := by
-- proof
  apply StatMech.Percolation.stt_reachable_iff ω n a b

/--
[stt_lex_ne_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_lex_ne_fst_eq
  {d : ℕ}
  {a₁ a₂ b₁ b₂ : ℕ}
-- given
  (h : a₁ ≠ a₂) :
-- imply
  (toLex (a₁, b₁)) ≠ toLex (a₂, b₂) := by
-- proof
  apply StatMech.Percolation.stt_lex_ne_fst h

/--
[stt_lex_ne_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_lex_ne_snd_eq
  {d : ℕ}
  {a b₁ b₂ : ℕ}
-- given
  (h : b₁ ≠ b₂) :
-- imply
  (toLex (a, b₁)) ≠ toLex (a, b₂) := by
-- proof
  apply StatMech.Percolation.stt_lex_ne_snd h

/--
[stt_lex_lt_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_lex_lt_fst_eq
  {d : ℕ}
  {a₁ a₂ b₁ b₂ : ℕ}
-- given
  (h : a₁ < a₂) :
-- imply
  (toLex (a₁, b₁)) < toLex (a₂, b₂) := by
-- proof
  apply StatMech.Percolation.stt_lex_lt_fst h

/--
[stt_lex_not_lt_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_lex_not_lt_fst_eq
  {d : ℕ}
  {a₁ a₂ b₁ b₂ : ℕ}
-- given
  (h : a₁ < a₂) :
-- imply
  ¬ ((toLex (a₂, b₂)) < toLex (a₁, b₁)) := by
-- proof
  apply StatMech.Percolation.stt_lex_not_lt_fst h

/--
[stt_exists_depthRank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_exists_depthRank_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  ∃ rank : Site d → ℕ ×ₗ ℕ, ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y := by
-- proof
  apply StatMech.Percolation.stt_exists_depthRank ω n

/--
[stt_rootedColoredForest_of_rootedSpanningForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_rootedColoredForest_of_rootedSpanningForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : stt_RootedSpanningForest ω n) :
-- imply
  rts_RootedColoredForest ω n := by
-- proof
  apply StatMech.Percolation.stt_rootedColoredForest_of_rootedSpanningForest ω n h

/--
[stt_rootedTreeArmSelection_of_rootedSpanningForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_rootedTreeArmSelection_of_rootedSpanningForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : stt_RootedSpanningForest ω n) :
-- imply
  bas_RootedTreeArmSelection ω n := by
-- proof
  apply StatMech.Percolation.stt_rootedTreeArmSelection_of_rootedSpanningForest ω n h

/--
[stt_rootedSpanningForest_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_rootedSpanningForest_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  stt_RootedSpanningForest ω n := by
-- proof
  apply StatMech.Percolation.stt_rootedSpanningForest_of_noTrif ω n hno

/--
[stt_rootedSpanningForest_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_rootedSpanningForest_of_twoTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
  {b : Site d → Site d}
  {cx0 cy0 : Site d → Fin 3}
-- given
  (hx0y0 : x₀ ≠ y₀)
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
  (hcx0faith : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v → (cx0 u = cx0 v ↔ fsp_sameArm ω x₀ u v))
  (hcy0faith : ∀ u v, Connected d ω y₀ u → y₀ ≠ u → Connected d ω y₀ v → y₀ ≠ v → (cy0 u = cy0 v ↔ fsp_sameArm ω y₀ u v))
  (hdeep : cy0 (b x₀) ≠ cy0 (b y₀)) :
-- imply
  stt_RootedSpanningForest ω n := by
-- proof
  apply StatMech.Percolation.stt_rootedSpanningForest_of_twoTrif ω n b cx0 cy0 hx0y0 htwo hbx0 hby0 hcx0faith hcy0faith hdeep

/--
[stt_rootedSpanningForest_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_rootedSpanningForest_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
  {lx : Site d → Fin 3}
  {ly : Fin 3 → Site d → Fin 3}
  {b : Site d → Site d}
  {j₀ : Fin 3}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
  (hyinj : Function.Injective y)
  (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v → (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
  (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v → (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
  (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w → (ly i w = 0 ↔ lx w ≠ i))
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hcy : ∀ i, lx (b (y i)) = i)
  (hcx : lx (b x₀) = j₀)
  (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
-- imply
  stt_RootedSpanningForest ω n := by
-- proof
  apply StatMech.Percolation.stt_rootedSpanningForest_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlxf hlyf hGstar hsingle b hbdata hcy hcx hcentral

/--
[stt_rootedSpanningForest_of_tree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_rootedSpanningForest_of_tree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {r m : Site d}
  {g : Fin 2 → Site d}
  {b : Site d → Site d}
  {cr cm : Site d → Fin 3}
  {cg : Fin 2 → Site d → Fin 3}
-- given
  (hdistinct : r ≠ m ∧ (∀ i, r ≠ g i) ∧ (∀ i, m ≠ g i) ∧ Function.Injective g)
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = r ∨ x = m ∨ ∃ i, x = g i)
  (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hcrf : ∀ u v, Connected d ω r u → r ≠ u → Connected d ω r v → r ≠ v → (cr u = cr v ↔ fsp_sameArm ω r u v))
  (hcmf : ∀ u v, Connected d ω m u → m ≠ u → Connected d ω m v → m ≠ v → (cm u = cm v ↔ fsp_sameArm ω m u v))
  (hcgf : ∀ i u v, Connected d ω (g i) u → g i ≠ u → Connected d ω (g i) v → g i ≠ v → (cg i u = cg i v ↔ fsp_sameArm ω (g i) u v))
  (hrm : cm (b r) ≠ cm (b m))
  (hrg : ∀ i, cg i (b r) ≠ cg i (b (g i)))
  (hmg : ∀ i, cg i (b m) ≠ cg i (b (g i)))
  (hgg : cg 1 (b (g 0)) ≠ cg 1 (b (g 1))) :
-- imply
  stt_RootedSpanningForest ω n := by
-- proof
  apply StatMech.Percolation.stt_rootedSpanningForest_of_tree ω n r m g b cr cm cg hdistinct hsingle hbdata hcrf hcmf hcgf hrm hrg hmg hgg

/--
[stt_Tcount_le_boundary_of_rootedSpanningForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_Tcount_le_boundary_of_rootedSpanningForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : stt_RootedSpanningForest ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.stt_Tcount_le_boundary_of_rootedSpanningForest ω n hn h

/--
[stt_burton_keane_bernoulli_of_rootedSpanningForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean)
-/
@[path]
private lemma stt_burton_keane_bernoulli_of_rootedSpanningForest_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → stt_RootedSpanningForest ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.stt_burton_keane_bernoulli_of_rootedSpanningForest hd p hp1 hp0 hres htrif


-- created on 2026-10-23
