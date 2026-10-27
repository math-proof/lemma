import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc77bdirect.Part2
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc77b_ox_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_ox_in_K_eq
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
  apply StatMech.Walls.gc77b_ox_in_K ends hnd hox hKsrc

/--
[gc77b_ox_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_ox_survives_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D : Finset ι}
  {o x : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hDV : D ⊆ univ \ K) :
-- imply
  connK ends ((K ∪ L) \ D) o x := by
-- proof
  apply StatMech.Walls.gc77b_ox_survives ends hnd hox hKsrc hDV

/--
[gc77b_og_survives_of_ogInK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_og_survives_of_ogInK_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D : Finset ι}
  {o g : W}
-- given
  (hDV : D ⊆ univ \ K)
  (hogK : connK ends K o g) :
-- imply
  connK ends ((K ∪ L) \ D) o g := by
-- proof
  apply StatMech.Walls.gc77b_og_survives_of_ogInK ends hDV hogK

/--
[gc77b_twoCommodityLeaf_of_ogInK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_twoCommodityLeaf_of_ogInK_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hogK : connK ends K o g) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g := by
-- proof
  apply StatMech.Walls.gc77b_twoCommodityLeaf_of_ogInK ends hnd K hoy hog hxy hxg hyg huniv hKsrc hogK

/--
[gc77b_ogSurvives_iff_xgSurvives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_ogSurvives_iff_xgSurvives_eq
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
  apply StatMech.Walls.gc77b_ogSurvives_iff_xgSurvives ends hnd hox hKsrc hDV

/--
[gc77b_leaf_of_xgSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_leaf_of_xgSurvival_eq
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
  apply StatMech.Walls.gc77b_leaf_of_xgSurvival ends hnd K hox hog hKsrc hDV hDsrc hD1 hxg

/--
[gc77b_twoCommodityLeaf_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_twoCommodityLeaf_dichotomy_eq
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
  (hcov : connK ends K o g ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1 ∧ ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g)) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g := by
-- proof
  apply StatMech.Walls.gc77b_twoCommodityLeaf_dichotomy ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc hcov

/--
[gc77b_starEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_starEnds_loopless_eq :
-- imply
  ∀ i : Fin 6, ¬ (gc77b_starEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc77b_starEnds_loopless

/--
[gc77b_starEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_starEnds_univ_sources_eq :
-- imply
  sources gc77b_starEnds (univ : Finset (Fin 6)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc77b_starEnds_univ_sources

/--
[gc77b_starEnds_K_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_starEnds_K_sources_eq :
-- imply
  sources gc77b_starEnds ({0, 1, 2} : Finset (Fin 6)) = ({0, 1} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc77b_starEnds_K_sources

/--
[gc77b_starEnds_g_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_starEnds_g_deg_eq :
-- imply
  degK gc77b_starEnds (univ : Finset (Fin 6)) 3 = 5 := by
-- proof
  apply StatMech.Walls.gc77b_starEnds_g_deg

/--
[gc77b_starEnds_og_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_starEnds_og_in_K_eq :
-- imply
  connK gc77b_starEnds ({0, 1, 2} : Finset (Fin 6)) 0 3 := by
-- proof
  apply StatMech.Walls.gc77b_starEnds_og_in_K

/--
[gc77b_star_twoCommodityLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_star_twoCommodityLeaf_eq :
-- imply
  gc71_TwoCommodityLeaf gc77b_starEnds ({0, 1, 2} : Finset (Fin 6)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc77b_star_twoCommodityLeaf

/--
[gc77b_hard_twoCommodity_content](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_hard_twoCommodity_content_eq :
-- imply
  (¬ connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3) ∧ connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc77b_hard_twoCommodity_content

/--
[gc77b_hard_og_not_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_hard_og_not_in_K_eq :
-- imply
  ¬ connK gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 3 := by
-- proof
  apply StatMech.Walls.gc77b_hard_og_not_in_K

/--
[gc77b_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean)
-/
@[path]
private lemma gc77b_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x : W), o ≠ x → sources ends K = ({o, x} : Finset W) → connK ends K o x) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W), o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g → sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) → sources ends K = ({o, x} : Finset W) → connK ends K o g → gc71_TwoCommodityLeaf ends K o x y g) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K L D : Finset ι) (o x g : W), o ≠ x → sources ends K = ({o, x} : Finset W) → D ⊆ univ \ K → (connK ends ((K ∪ L) \ D) x g ↔ connK ends ((K ∪ L) \ D) o g)) ∧ gc71_TwoCommodityLeaf gc77b_starEnds ({0, 1, 2} : Finset (Fin 6)) 0 1 2 3 ∧ ((¬ connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3) ∧ connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3) := by
-- proof
  apply StatMech.Walls.gc77b_status


-- created on 2026-10-23
