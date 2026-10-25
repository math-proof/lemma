import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc72twogedge.Part2
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc72_trim_to_ogBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc72twogedge.lean)
-/
@[path]
private lemma gc72_trim_to_ogBoundary_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G D : Finset ι}
  {o g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g)
  (hconn : connK ends (G \ D) o g) :
-- imply
  ∃ P, P ⊆ G ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g := by
-- proof
  apply StatMech.Walls.gc72_trim_to_ogBoundary ends hnd hog hconn

/--
[gc72_twoCommodityLeaf_of_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc72twogedge.lean)
-/
@[path]
private lemma gc72_twoCommodityLeaf_of_removalSurvival_eq
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
  (hog : o ≠ g)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (h : gc66_GDeg1RemovalSurvival ends K o x y g) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g := by
-- proof
  apply StatMech.Walls.gc72_twoCommodityLeaf_of_removalSurvival ends hnd K hox hog hKsrc h

/--
[gc72_twoCommodityLeaf_iff_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc72twogedge.lean)
-/
@[path]
private lemma gc72_twoCommodityLeaf_iff_removalSurvival_eq
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
  (hog : o ≠ g)
  (hKsrc : sources ends K = ({o, x} : Finset W)) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g ↔ gc66_GDeg1RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc72_twoCommodityLeaf_iff_removalSurvival ends hnd K hox hog hKsrc

/--
[gc72_leafClause_iff_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc72twogedge.lean)
-/
@[path]
private lemma gc72_leafClause_iff_survives_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D : Finset ι}
  {o g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g) :
-- imply
  (∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g) ↔ connK ends ((K ∪ L) \ D) o g := by
-- proof
  apply StatMech.Walls.gc72_leafClause_iff_survives ends hnd hog

/--
[gc72_ogSurvives_of_relConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc72twogedge.lean)
-/
@[path]
private lemma gc72_ogSurvives_of_relConn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {o g : W}
  {D : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g)
  (hconn : connK ends G o g)
  (hrel : ∀ P₁ : Finset ι, P₁ ⊆ G → sources ends P₁ = ({o, g} : Finset W) → connK ends (G \ P₁) o g)
  (hDsub : ∃ P₁ : Finset ι, P₁ ⊆ G ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁) :
-- imply
  ∃ P, P ⊆ G ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g := by
-- proof
  apply StatMech.Walls.gc72_ogSurvives_of_relConn ends hnd hog hconn hrel hDsub

/--
[gc72_og_in_KL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc72twogedge.lean)
-/
@[path]
private lemma gc72_og_in_KL_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x g : W}
  {L : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hL : L ∈ gc51_LblockSet ends K o x g) :
-- imply
  connK ends (K ∪ L) o g := by
-- proof
  apply StatMech.Walls.gc72_og_in_KL ends hnd K hox hKsrc hL

/--
[gc72_twoCommodityLeaf_of_relConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc72twogedge.lean)
-/
@[path]
private lemma gc72_twoCommodityLeaf_of_relConn_eq
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
  (hrel : ∀ L ∈ gc51_LblockSet ends K o x g, (∀ P₁ : Finset ι, P₁ ⊆ K ∪ L → sources ends P₁ = ({o, g} : Finset W) → connK ends ((K ∪ L) \ P₁) o g) ∧ (∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁)) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g := by
-- proof
  apply StatMech.Walls.gc72_twoCommodityLeaf_of_relConn ends hnd K hox hog hKsrc hDV hDsrc hD1 hrel

/--
[gc72_gc59_connectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc72twogedge.lean)
-/
@[path]
private lemma gc72_gc59_connectors_eq :
-- imply
  ((({1, 2, 3, 4} : Finset (Fin 5)).powerset).filter (fun D => sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) ∧ degK gc59_witnessEnds D 3 = 1)) = ({({1, 2} : Finset (Fin 5)), ({1, 3} : Finset (Fin 5)), ({1, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5))) := by
-- proof
  apply StatMech.Walls.gc72_gc59_connectors

/--
[gc72_no_oAvoiding_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc72twogedge.lean)
-/
@[path]
private lemma gc72_no_oAvoiding_connector_eq :
-- imply
  ∀ D : Finset (Fin 5), D ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) → sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) → degK gc59_witnessEnds D 3 = 1 → ¬ gc72_AvoidsO gc59_witnessEnds D 0 := by
-- proof
  apply StatMech.Walls.gc72_no_oAvoiding_connector

/--
[gc72_oAvoiding_construction_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc72twogedge.lean)
-/
@[path]
private lemma gc72_oAvoiding_construction_refuted_eq :
-- imply
  (∀ D : Finset (Fin 5), D ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) → sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) → degK gc59_witnessEnds D 3 = 1 → ¬ gc72_AvoidsO gc59_witnessEnds D 0) ∧ gc71_TwoCommodityLeaf gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc72_oAvoiding_construction_refuted

/--
[gc72_witness_twoCommodityLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc72twogedge.lean)
-/
@[path]
private lemma gc72_witness_twoCommodityLeaf_eq :
-- imply
  gc71_TwoCommodityLeaf gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc72_witness_twoCommodityLeaf

/--
[gc72_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc72twogedge.lean)
-/
@[path]
private lemma gc72_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W), o ≠ x → o ≠ g → sources ends K = ({o, x} : Finset W) → (gc71_TwoCommodityLeaf ends K o x y g ↔ gc66_GDeg1RemovalSurvival ends K o x y g)) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W) (D : Finset ι), o ≠ x → o ≠ g → sources ends K = ({o, x} : Finset W) → D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) → degK ends D g = 1 → (∀ L ∈ gc51_LblockSet ends K o x g, (∀ P₁ : Finset ι, P₁ ⊆ K ∪ L → sources ends P₁ = ({o, g} : Finset W) → connK ends ((K ∪ L) \ P₁) o g) ∧ (∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁)) → gc71_TwoCommodityLeaf ends K o x y g) ∧ ((∀ D : Finset (Fin 5), D ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) → sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) → degK gc59_witnessEnds D 3 = 1 → ¬ gc72_AvoidsO gc59_witnessEnds D 0) ∧ gc71_TwoCommodityLeaf gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3) ∧ gc71_TwoCommodityLeaf gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc72_status


-- created on 2026-10-23
