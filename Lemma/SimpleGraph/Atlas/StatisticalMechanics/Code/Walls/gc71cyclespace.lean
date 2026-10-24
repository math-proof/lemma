import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc71cyclespace
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc71_room_of_gDeg1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma gc71_room_of_gDeg1_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {D : Finset ι}
  {g : W}
-- given
  (hge3 : 3 ≤ degK ends (univ : Finset ι) g)
  (hD1 : degK ends D g = 1) :
-- imply
  2 ≤ degK ends ((univ : Finset ι) \ D) g := by
-- proof
  apply StatMech.Walls.gc71_room_of_gDeg1 ends hge3 hD1

/--
[gc71_minConnector_gDeg1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma gc71_minConnector_gDeg1_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {y g : W}
  {D : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hyg : y ≠ g)
  (hDV : D ⊆ univ \ K)
  (hDsrc : sources ends D = ({y, g} : Finset W))
  (hDmin : ∀ D', D' ⊆ univ \ K → sources ends D' = ({y, g} : Finset W) → #D ≤ #D') :
-- imply
  degK ends D g = 1 := by
-- proof
  apply StatMech.Walls.gc71_minConnector_gDeg1 ends hnd K hyg hDV hDsrc hDmin

/--
[gc71_gc66_of_gDeg1Data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma gc71_gc66_of_gDeg1Data_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {D : Finset ι}
-- given
  (hDV : D ⊆ univ \ K)
  (hDsrc : sources ends D = ({y, g} : Finset W))
  (hD1 : degK ends D g = 1)
  (hsurv : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g) :
-- imply
  gc66_GDeg1RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc71_gc66_of_gDeg1Data ends K hDV hDsrc hD1 hsurv

/--
[gc71_countIneq_of_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma gc71_countIneq_of_removalSurvival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
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
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc66_GDeg1RemovalSurvival ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc71_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc71_gc66_of_twoCommodityLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma gc71_gc66_of_twoCommodityLeaf_eq
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
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (h : gc71_TwoCommodityLeaf ends K o x y g) :
-- imply
  gc66_GDeg1RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc71_gc66_of_twoCommodityLeaf ends hnd K hox hKsrc h

/--
[gc71_countIneq_of_twoCommodityLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma gc71_countIneq_of_twoCommodityLeaf_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
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
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc71_TwoCommodityLeaf ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc71_countIneq_of_twoCommodityLeaf ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[ceEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_loopless_eq :
-- imply
  ∀ i : Fin 10, ¬ (ceEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.ceEnds_loopless

/--
[ceEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_univ_sources_eq :
-- imply
  sources ceEnds (univ : Finset (Fin 10)) = ({0, 1, 2, 3} : Finset (Fin 6)) := by
-- proof
  apply StatMech.Walls.ceEnds_univ_sources

/--
[ceEnds_K_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_K_sources_eq :
-- imply
  sources ceEnds ({4} : Finset (Fin 10)) = ({0, 1} : Finset (Fin 6)) := by
-- proof
  apply StatMech.Walls.ceEnds_K_sources

/--
[ceEnds_V_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_V_eq_eq :
-- imply
  (univ : Finset (Fin 10)) \ ({4} : Finset (Fin 10)) = ({0, 1, 2, 3, 5, 6, 7, 8, 9} : Finset (Fin 10)) := by
-- proof
  apply StatMech.Walls.ceEnds_V_eq

/--
[ceEnds_no_lowCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_no_lowCard_eq :
-- imply
  ((({0, 1, 2, 3, 5, 6, 7, 8, 9} : Finset (Fin 10)).powerset.filter (fun D => #D ≤ 1)).filter (fun D => sources ceEnds D = ({2, 3} : Finset (Fin 6)))) = (∅ : Finset (Finset (Fin 10))) := by
-- proof
  apply StatMech.Walls.ceEnds_no_lowCard

/--
[ceEnds_card2_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_card2_unique_eq :
-- imply
  ((({0, 1, 2, 3, 5, 6, 7, 8, 9} : Finset (Fin 10)).powerset.filter (fun D => #D ≤ 2)).filter (fun D => sources ceEnds D = ({2, 3} : Finset (Fin 6)))) = {({0, 9} : Finset (Fin 10))} := by
-- proof
  apply StatMech.Walls.ceEnds_card2_unique

/--
[ceEnds_minCard_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_minCard_unique_eq
  {D' : Finset (Fin 10)}
-- given
  (hD'V : D' ⊆ ({0, 1, 2, 3, 5, 6, 7, 8, 9} : Finset (Fin 10)))
  (hD'src : sources ceEnds D' = ({2, 3} : Finset (Fin 6)))
  (hD'card : #D' ≤ 2) :
-- imply
  D' = ({0, 9} : Finset (Fin 10)) := by
-- proof
  apply StatMech.Walls.ceEnds_minCard_unique hD'V hD'src hD'card

/--
[ceEnds_D09_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_D09_sources_eq :
-- imply
  sources ceEnds ({0, 9} : Finset (Fin 10)) = ({2, 3} : Finset (Fin 6)) := by
-- proof
  apply StatMech.Walls.ceEnds_D09_sources

/--
[ceEnds_D09_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_D09_subset_eq :
-- imply
  ({0, 9} : Finset (Fin 10)) ⊆ (univ : Finset (Fin 10)) \ ({4} : Finset (Fin 10)) := by
-- proof
  apply StatMech.Walls.ceEnds_D09_subset

/--
[ceEnds_L_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_L_sources_eq :
-- imply
  sources ceEnds ({0, 1, 2, 3, 9} : Finset (Fin 10)) = (∅ : Finset (Fin 6)) := by
-- proof
  apply StatMech.Walls.ceEnds_L_sources

/--
[ceEnds_L_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_L_subset_eq :
-- imply
  ({0, 1, 2, 3, 9} : Finset (Fin 10)) ⊆ (univ : Finset (Fin 10)) \ ({4} : Finset (Fin 10)) := by
-- proof
  apply StatMech.Walls.ceEnds_L_subset

/--
[ceEnds_gate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_gate_eq :
-- imply
  connK ceEnds (({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10))) 1 3 := by
-- proof
  apply StatMech.Walls.ceEnds_gate

/--
[ceEnds_not_conn_of_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_not_conn_of_invariant_eq
  {G : Finset (Fin 10)}
  {a b : Fin 6}
  [DecidablePred C]
-- given
  (C : Fin 6 → Prop)
  (hCa : C a)
  (hCb : ¬ C b)
  (hclosed : ∀ c d : Fin 6, C c → (∃ i ∈ G, c ∈ ceEnds i ∧ d ∈ ceEnds i ∧ c ≠ d) → C d) :
-- imply
  ¬ connK ceEnds G a b := by
-- proof
  apply StatMech.Walls.ceEnds_not_conn_of_invariant G C hCa hCb hclosed

/--
[ceEnds_D09_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_D09_fails_eq :
-- imply
  ¬ connK ceEnds ((({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10))) \ ({0, 9} : Finset (Fin 10))) 0 3 := by
-- proof
  apply StatMech.Walls.ceEnds_D09_fails

/--
[ceEnds_L_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_L_mem_eq :
-- imply
  ({0, 1, 2, 3, 9} : Finset (Fin 10)) ∈ gc51_LblockSet ceEnds ({4} : Finset (Fin 10)) 0 1 3 := by
-- proof
  apply StatMech.Walls.ceEnds_L_mem

/--
[gc71_minCardResidue_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma gc71_minCardResidue_false_eq :
-- imply
  ¬ gc70b_OGConnAvoidingD ceEnds ({4} : Finset (Fin 10)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc71_minCardResidue_false

/--
[gc71_ogSurvival_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma gc71_ogSurvival_false_eq :
-- imply
  ¬ gc69b_OGSurvival ceEnds ({4} : Finset (Fin 10)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc71_ogSurvival_false

/--
[ceEnds_D123_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_D123_sources_eq :
-- imply
  sources ceEnds ({1, 2, 3} : Finset (Fin 10)) = ({2, 3} : Finset (Fin 6)) := by
-- proof
  apply StatMech.Walls.ceEnds_D123_sources

/--
[ceEnds_D123_gDeg1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_D123_gDeg1_eq :
-- imply
  degK ceEnds ({1, 2, 3} : Finset (Fin 10)) 3 = 1 := by
-- proof
  apply StatMech.Walls.ceEnds_D123_gDeg1

/--
[ceEnds_D123_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_D123_subset_eq :
-- imply
  ({1, 2, 3} : Finset (Fin 10)) ⊆ (univ : Finset (Fin 10)) \ ({4} : Finset (Fin 10)) := by
-- proof
  apply StatMech.Walls.ceEnds_D123_subset

/--
[ceEnds_D123_notMinCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_D123_notMinCard_eq :
-- imply
  #({0, 9} : Finset (Fin 10)) < #({1, 2, 3} : Finset (Fin 10)) := by
-- proof
  apply StatMech.Walls.ceEnds_D123_notMinCard

/--
[ceEnds_P0_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_P0_sources_eq :
-- imply
  sources ceEnds ({0} : Finset (Fin 10)) = ({0, 3} : Finset (Fin 6)) := by
-- proof
  apply StatMech.Walls.ceEnds_P0_sources

/--
[ceEnds_P0_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma ceEnds_P0_conn_eq :
-- imply
  connK ceEnds ({0} : Finset (Fin 10)) 0 3 := by
-- proof
  apply StatMech.Walls.ceEnds_P0_conn

/--
[gc71_ce_gDeg1_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma gc71_ce_gDeg1_witness_eq :
-- imply
  ∃ D', D' ⊆ univ \ ({4} : Finset (Fin 10)) ∧ sources ceEnds D' = ({2, 3} : Finset (Fin 6)) ∧ degK ceEnds D' 3 = 1 ∧ #({0, 9} : Finset (Fin 10)) < #D' ∧ ∃ P, P ⊆ ({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10)) ∧ sources ceEnds P = ({0, 3} : Finset (Fin 6)) ∧ Disjoint P D' ∧ connK ceEnds P 0 3 ∧ connK ceEnds ((({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10))) \ D') 0 3 := by
-- proof
  apply StatMech.Walls.gc71_ce_gDeg1_witness

/--
[gc71_witness_gc66](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma gc71_witness_gc66_eq :
-- imply
  gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc71_witness_gc66

/--
[gc71_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean)
-/
@[path]
private lemma gc71_status_eq :
-- imply
  (¬ gc70b_OGConnAvoidingD ceEnds ({4} : Finset (Fin 10)) 0 1 2 3) ∧ (¬ gc69b_OGSurvival ceEnds ({4} : Finset (Fin 10)) 0 1 2 3) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (o x y g : W), o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g → sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) → (∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc66_GDeg1RemovalSurvival ends K o x y g) → gc39_ThreeColouringCountIneq ends o x y g) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (o x y g : W), o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g → sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) → (∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc71_TwoCommodityLeaf ends K o x y g) → gc39_ThreeColouringCountIneq ends o x y g) ∧ (∃ D', D' ⊆ univ \ ({4} : Finset (Fin 10)) ∧ sources ceEnds D' = ({2, 3} : Finset (Fin 6)) ∧ degK ceEnds D' 3 = 1 ∧ #({0, 9} : Finset (Fin 10)) < #D' ∧ ∃ P, P ⊆ ({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10)) ∧ sources ceEnds P = ({0, 3} : Finset (Fin 6)) ∧ Disjoint P D' ∧ connK ceEnds P 0 3 ∧ connK ceEnds ((({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10))) \ D') 0 3) ∧ gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc71_status


-- created on 2026-10-23
