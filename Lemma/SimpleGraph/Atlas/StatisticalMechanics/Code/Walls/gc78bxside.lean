import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc78bxside
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc78b_ox_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_ox_in_K_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hKsrc : sources ends K = ({o, x} : Finset W)) :
-- imply
  connK ends K o x := by
-- proof
  apply StatMech.Walls.gc78b_ox_in_K ends hnd hox hKsrc

/--
[gc78b_xg_in_K_iff_og_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xg_in_K_iff_og_in_K_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hKsrc : sources ends K = ({o, x} : Finset W)) :
-- imply
  connK ends K x g ↔ connK ends K o g := by
-- proof
  apply StatMech.Walls.gc78b_xg_in_K_iff_og_in_K ends hnd hox hKsrc

/--
[gc78b_twoCommodityLeaf_of_xgInK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_twoCommodityLeaf_of_xgInK_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hxgK : connK ends K x g) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g := by
-- proof
  apply StatMech.Walls.gc78b_twoCommodityLeaf_of_xgInK ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc hxgK

/--
[gc78b_xgSurvives_iff_ogSurvives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xgSurvives_iff_ogSurvives_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D : Finset ι}
  {o x g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hDV : D ⊆ univ \ K) :
-- imply
  connK ends ((K ∪ L) \ D) x g ↔ connK ends ((K ∪ L) \ D) o g := by
-- proof
  apply StatMech.Walls.gc78b_xgSurvives_iff_ogSurvives ends hnd hox hKsrc hDV

/--
[gc78b_leaf_of_xgSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_leaf_of_xgSurvival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {D : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hog : o ≠ g)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hDV : D ⊆ univ \ K)
  (hDsrc : sources ends D = ({y, g} : Finset W))
  (hD1 : degK ends D g = 1)
  (hxg : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g := by
-- proof
  apply StatMech.Walls.gc78b_leaf_of_xgSurvival ends hnd K hox hog hKsrc hDV hDsrc hD1 hxg

/--
[gc78b_twoCommodityLeaf_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_twoCommodityLeaf_dichotomy_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hcov : connK ends K x g ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1 ∧ ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g)) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g := by
-- proof
  apply StatMech.Walls.gc78b_twoCommodityLeaf_dichotomy ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc hcov

/--
[gc78b_xEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xEnds_loopless_eq :
-- imply
  ∀ i : Fin 7, ¬ (gc78b_xEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc78b_xEnds_loopless

/--
[gc78b_xEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xEnds_univ_sources_eq :
-- imply
  sources gc78b_xEnds (univ : Finset (Fin 7)) = ({0, 1, 2, 3} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc78b_xEnds_univ_sources

/--
[gc78b_xEnds_K_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xEnds_K_sources_eq :
-- imply
  sources gc78b_xEnds ({2} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc78b_xEnds_K_sources

/--
[gc78b_xEnds_g_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xEnds_g_deg3_eq :
-- imply
  degK gc78b_xEnds (univ : Finset (Fin 7)) 3 = 3 := by
-- proof
  apply StatMech.Walls.gc78b_xEnds_g_deg3

/--
[gc78b_xEnds_og_not_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xEnds_og_not_in_K_eq :
-- imply
  ¬ connK gc78b_xEnds ({2} : Finset (Fin 7)) 0 3 := by
-- proof
  apply StatMech.Walls.gc78b_xEnds_og_not_in_K

/--
[gc78b_xEnds_xg_not_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xEnds_xg_not_in_K_eq :
-- imply
  ¬ connK gc78b_xEnds ({2} : Finset (Fin 7)) 1 3 := by
-- proof
  apply StatMech.Walls.gc78b_xEnds_xg_not_in_K

/--
[gc78b_xEnds_L_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xEnds_L_sources_eq :
-- imply
  sources gc78b_xEnds ({0, 3, 5, 6} : Finset (Fin 7)) = (∅ : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc78b_xEnds_L_sources

/--
[gc78b_xEnds_gate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xEnds_gate_eq :
-- imply
  connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc78b_xEnds_gate

/--
[gc78b_xEnds_mincardD_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xEnds_mincardD_data_eq :
-- imply
  ({0, 3} : Finset (Fin 7)) ⊆ (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7)) ∧ sources gc78b_xEnds ({0, 3} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) ∧ degK gc78b_xEnds ({0, 3} : Finset (Fin 7)) 3 = 1 := by
-- proof
  apply StatMech.Walls.gc78b_xEnds_mincardD_data

/--
[gc78b_xEnds_workingD_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xEnds_workingD_data_eq :
-- imply
  ({5, 6} : Finset (Fin 7)) ⊆ (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7)) ∧ sources gc78b_xEnds ({5, 6} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) ∧ degK gc78b_xEnds ({5, 6} : Finset (Fin 7)) 3 = 1 := by
-- proof
  apply StatMech.Walls.gc78b_xEnds_workingD_data

/--
[gc78b_mincard_D_fails_xg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_mincard_D_fails_xg_eq :
-- imply
  ¬ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc78b_mincard_D_fails_xg

/--
[gc78b_mincard_D_fails_og](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_mincard_D_fails_og_eq :
-- imply
  ¬ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))) 0 3 := by
-- proof
  apply StatMech.Walls.gc78b_mincard_D_fails_og

/--
[gc78b_working_D_works_xg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_working_D_works_xg_eq :
-- imply
  connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc78b_working_D_works_xg

/--
[gc78b_xside_no_canonical_D](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_xside_no_canonical_D_eq :
-- imply
  (({0, 3} : Finset (Fin 7)) ⊆ (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7)) ∧ sources gc78b_xEnds ({0, 3} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) ∧ degK gc78b_xEnds ({0, 3} : Finset (Fin 7)) 3 = 1) ∧ (({5, 6} : Finset (Fin 7)) ⊆ (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7)) ∧ sources gc78b_xEnds ({5, 6} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) ∧ degK gc78b_xEnds ({5, 6} : Finset (Fin 7)) 3 = 1) ∧ (¬ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))) 1 3) ∧ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc78b_xside_no_canonical_D

/--
[gc78b_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean)
-/
@[path]
private lemma gc78b_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x g : W), o ≠ x → sources ends K = ({o, x} : Finset W) → (connK ends K x g ↔ connK ends K o g)) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W), o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g → sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) → sources ends K = ({o, x} : Finset W) → connK ends K x g → gc71_TwoCommodityLeaf ends K o x y g) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K L D : Finset ι) (o x g : W), o ≠ x → sources ends K = ({o, x} : Finset W) → D ⊆ univ \ K → (connK ends ((K ∪ L) \ D) x g ↔ connK ends ((K ∪ L) \ D) o g)) ∧ ((¬ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))) 1 3) ∧ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 1 3) ∧ (¬ connK gc78b_xEnds ({2} : Finset (Fin 7)) 1 3) := by
-- proof
  apply StatMech.Walls.gc78b_status


-- created on 2026-10-23
