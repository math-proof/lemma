import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc69mengerclose.Part4
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc69b_ogReroute_of_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_ogReroute_of_disjointConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D P : Finset ι}
  {o g : W}
-- given
  (hPG : P ⊆ K ∪ L)
  (hPD : Disjoint P D)
  (hPconn : connK ends P o g) :
-- imply
  connK ends ((K ∪ L) \ D) o g := by
-- proof
  apply StatMech.Walls.gc69b_ogReroute_of_disjointConnector ends hPG hPD hPconn

/--
[gc69b_disjointConnector_of_ogReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_disjointConnector_of_ogReroute_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D : Finset ι}
  {o g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g)
  (hsurv : connK ends ((K ∪ L) \ D) o g) :
-- imply
  ∃ P, P ⊆ K ∪ L ∧ Disjoint P D ∧ sources ends P = ({o, g} : Finset W) ∧ connK ends P o g := by
-- proof
  apply StatMech.Walls.gc69b_disjointConnector_of_ogReroute ends hnd hog hsurv

/--
[gc69b_not_isCut_of_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_not_isCut_of_disjointConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D P : Finset ι}
  {o g : W}
-- given
  (hPG : P ⊆ K ∪ L)
  (hPD : Disjoint P D)
  (hPconn : connK ends P o g) :
-- imply
  ¬ mngg_IsCut ends (K ∪ L) o g D := by
-- proof
  apply StatMech.Walls.gc69b_not_isCut_of_disjointConnector ends hPG hPD hPconn

/--
[gc69b_ogReroute_of_disjointOGConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_ogReroute_of_disjointOGConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (h : gc69b_DisjointOGConnector ends K o x y g) :
-- imply
  gc68_OGReroute ends K o x y g := by
-- proof
  apply StatMech.Walls.gc69b_ogReroute_of_disjointOGConnector ends K h

/--
[gc69b_disjointOGConnector_of_ogReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_disjointOGConnector_of_ogReroute_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g)
  (h : gc68_OGReroute ends K o x y g) :
-- imply
  gc69b_DisjointOGConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc69b_disjointOGConnector_of_ogReroute ends hnd K hog h

/--
[gc69b_ogReroute_iff_disjointOGConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_ogReroute_iff_disjointOGConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g) :
-- imply
  gc68_OGReroute ends K o x y g ↔ gc69b_DisjointOGConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc69b_ogReroute_iff_disjointOGConnector ends hnd K hog

/--
[gc69b_removalSurvival_of_disjointOGConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_removalSurvival_of_disjointOGConnector_eq
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
  (h : gc69b_DisjointOGConnector ends K o x y g) :
-- imply
  gc66_GDeg1RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc69b_removalSurvival_of_disjointOGConnector ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc h

/--
[gc69b_countIneq_of_disjointOGConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_countIneq_of_disjointOGConnector_eq
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
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc69b_DisjointOGConnector ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc69b_countIneq_of_disjointOGConnector ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc69b_minConnector_gDeg1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_minConnector_gDeg1_eq
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
  apply StatMech.Walls.gc69b_minConnector_gDeg1 ends hnd K hyg hDV hDsrc hDmin

/--
[gc69b_removalSurvival_of_ogSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_removalSurvival_of_ogSurvival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hyg : y ≠ g)
  (h : gc69b_OGSurvival ends K o x y g) :
-- imply
  gc66_GDeg1RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc69b_removalSurvival_of_ogSurvival ends hnd K hyg h

/--
[gc69b_countIneq_of_ogSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_countIneq_of_ogSurvival_eq
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
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc69b_OGSurvival ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc69b_countIneq_of_ogSurvival ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc69b_relConn2_false_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_relConn2_false_of_bridge_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G C : Finset ι}
  {o g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g)
  (hC : mngg_IsCut ends G o g C)
  (hC1 : #C = 1) :
-- imply
  ¬ mngg_RelConn ends G o g 2 := by
-- proof
  apply StatMech.Walls.gc69b_relConn2_false_of_bridge ends hnd hog hC hC1

/--
[gc69b_witness_disjointOGConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_witness_disjointOGConnector_eq :
-- imply
  gc69b_DisjointOGConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc69b_witness_disjointOGConnector

/--
[gc69b_witness_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_witness_removalSurvival_eq :
-- imply
  gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc69b_witness_removalSurvival

/--
[gc69b_witness_ogSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_witness_ogSurvival_eq :
-- imply
  gc69b_OGSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc69b_witness_ogSurvival

/--
[gc69b_witness_removalSurvival_via_ogSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_witness_removalSurvival_via_ogSurvival_eq :
-- imply
  gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc69b_witness_removalSurvival_via_ogSurvival

/--
[gc69b_bridge_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_bridge_loopless_eq :
-- imply
  ∀ i : Fin 1, ¬ (gc69b_bridgeEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc69b_bridge_loopless

/--
[gc69b_bridge_isCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_bridge_isCut_eq :
-- imply
  mngg_IsCut gc69b_bridgeEnds (univ : Finset (Fin 1)) 0 1 ({0} : Finset (Fin 1)) := by
-- proof
  apply StatMech.Walls.gc69b_bridge_isCut

/--
[gc69b_bridge_refutes_menger2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_bridge_refutes_menger2_eq :
-- imply
  ¬ mngg_RelConn gc69b_bridgeEnds (univ : Finset (Fin 1)) 0 1 2 := by
-- proof
  apply StatMech.Walls.gc69b_bridge_refutes_menger2

/--
[gc69b_refut_D12_min](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_refut_D12_min_eq
  {D' : Finset (Fin 7)}
-- given
  (hD'V : D' ⊆ (univ : Finset (Fin 7)) \ ({0} : Finset (Fin 7)))
  (hD'src : sources gc63b_refutEnds D' = ({2, 3} : Finset (Fin 5))) :
-- imply
  (#({1, 2} : Finset (Fin 7))) ≤ #D' := by
-- proof
  apply StatMech.Walls.gc69b_refut_D12_min D' hD'V hD'src

/--
[gc69b_ogReroute_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_ogReroute_false_eq :
-- imply
  ¬ gc68_OGReroute gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc69b_ogReroute_false

/--
[gc69b_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean)
-/
@[path]
private lemma gc69b_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W), o ≠ g → (gc68_OGReroute ends K o x y g ↔ gc69b_DisjointOGConnector ends K o x y g)) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (o x y g : W), o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g → sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) → (∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc69b_DisjointOGConnector ends K o x y g) → gc39_ThreeColouringCountIneq ends o x y g) ∧ (¬ mngg_RelConn gc69b_bridgeEnds (univ : Finset (Fin 1)) 0 1 2) ∧ (¬ gc68_OGReroute gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (o x y g : W), o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g → sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) → (∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc69b_OGSurvival ends K o x y g) → gc39_ThreeColouringCountIneq ends o x y g) ∧ gc69b_DisjointOGConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 ∧ gc69b_OGSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 ∧ gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc69b_status


-- created on 2026-10-23
