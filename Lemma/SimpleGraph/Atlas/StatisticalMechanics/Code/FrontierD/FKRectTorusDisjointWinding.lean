import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
open SimpleGraph StatMech StatMech.FrontierD StatMech.FrontierD.FKRectDartListUsesPoint


/--
[of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma of_mem_eq
  {L : Nat}
  {l : List (ons_Dart L)}
  {d : ons_Dart L}
-- given
  (hd : d ∈ l) :
-- imply
  FKRectDartListUsesPoint l d.1 := by
-- proof
  apply StatMech.FrontierD.FKRectDartListUsesPoint.of_mem hd

/--
[of_mem_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma of_mem_end_eq
  {L : Nat}
  {l : List (ons_Dart L)}
  {d : ons_Dart L}
-- given
  (hd : d ∈ l) :
-- imply
  FKRectDartListUsesPoint l (ons_dirStep L d.2 d.1) := by
-- proof
  apply StatMech.FrontierD.FKRectDartListUsesPoint.of_mem_end hd

/--
[of_horizontal_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma of_horizontal_ne_zero_eq
  {L : Nat}
  {l : List (ons_Dart L)}
  {p : ZMod L × ZMod L}
-- given
  (h : (l.map (fun d => IntegralSquareTorusCycle.dartHorizontal d p)).sum ≠ 0) :
-- imply
  FKRectDartListUsesPoint l p := by
-- proof
  apply StatMech.FrontierD.FKRectDartListUsesPoint.of_horizontal_ne_zero h

/--
[of_vertical_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma of_vertical_ne_zero_eq
  {L : Nat}
  {l : List (ons_Dart L)}
  {p : ZMod L × ZMod L}
-- given
  (h : (l.map (fun d => IntegralSquareTorusCycle.dartVertical d p)).sum ≠ 0) :
-- imply
  FKRectDartListUsesPoint l p := by
-- proof
  apply StatMech.FrontierD.FKRectDartListUsesPoint.of_vertical_ne_zero h

/--
[of_horizontal_ne_zero_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma of_horizontal_ne_zero_east_eq
  {L : Nat}
  {l : List (ons_Dart L)}
  {p : ZMod L × ZMod L}
-- given
  (h : (l.map (fun d => IntegralSquareTorusCycle.dartHorizontal d p)).sum ≠ 0) :
-- imply
  FKRectDartListUsesPoint l (p.1 + 1, p.2) := by
-- proof
  apply StatMech.FrontierD.FKRectDartListUsesPoint.of_horizontal_ne_zero_east h

/--
[of_vertical_ne_zero_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma of_vertical_ne_zero_north_eq
  {L : Nat}
  {l : List (ons_Dart L)}
  {p : ZMod L × ZMod L}
-- given
  (h : (l.map (fun d => IntegralSquareTorusCycle.dartVertical d p)).sum ≠ 0) :
-- imply
  FKRectDartListUsesPoint l (p.1, p.2 + 1) := by
-- proof
  apply StatMech.FrontierD.FKRectDartListUsesPoint.of_vertical_ne_zero_north h

/--
[IntegralSquareTorusCycle.ofDartList_locallyDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma ofDartList_locallyDisjoint_eq
  {L : Nat}
  [Fact (2 < L)]
  {v w : List (ons_Dart L)}
-- given
  (hv : IntegralSquareTorusCycle.DartListBalanced v)
  (hw : IntegralSquareTorusCycle.DartListBalanced w)
  (hdisj : ∀ p, FKRectDartListUsesPoint v p → ¬ FKRectDartListUsesPoint w p) :
-- imply
  (IntegralSquareTorusCycle.ofDartList v hv).LocallyDisjoint (IntegralSquareTorusCycle.ofDartList w hw) := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.ofDartList_locallyDisjoint v w hv hw hdisj

/--
[fkRectSquareRepresentativeVertex_eq_of_pointMod_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma fkRectSquareRepresentativeVertex_eq_of_pointMod_eq_eq
  {R : FKRectTorus}
  {a b : Int × Int}
-- given
  (hmod : fkRectIntegralSquarePointMod (fkRectSquareCoverSide R) a = fkRectIntegralSquarePointMod (fkRectSquareCoverSide R) b) :
-- imply
  fkRectSquareRepresentativeVertex R a = fkRectSquareRepresentativeVertex R b := by
-- proof
  apply StatMech.FrontierD.fkRectSquareRepresentativeVertex_eq_of_pointMod_eq R hmod

/--
[fkRectSquareRepresentativeVertex_add_deck](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma fkRectSquareRepresentativeVertex_add_deck_eq
  {R : FKRectTorus}
  {z u : Int × Int} :
-- imply
  fkRectSquareRepresentativeVertex R (z + fkRectSquareDeckTranslation R u) = fkRectSquareRepresentativeVertex R z := by
-- proof
  apply StatMech.FrontierD.fkRectSquareRepresentativeVertex_add_deck R z u

/--
[FKRectSquareWalkLift.exists_supportedIntegralDartPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma exists_supportedIntegralDartPath_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  ∃ l : List FKRectIntegralSquareDart, FKRectIntegralSquareDartPath (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) l ∧ ∀ d ∈ l, fkRectSquareRepresentativeVertex R d.1 ∈ w.support ∧ fkRectSquareRepresentativeVertex R (fkRectIntegralSquareDartEnd d) ∈ w.support := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.exists_supportedIntegralDartPath R h

/--
[fkRectNatScale_squareDeckTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma fkRectNatScale_squareDeckTranslation_eq
  {R : FKRectTorus}
  {n : Nat}
  {u : Int × Int} :
-- imply
  fkRectNatScale n (fkRectSquareDeckTranslation R u) = fkRectSquareDeckTranslation R ((n : Int) * u.1, (n : Int) * u.2) := by
-- proof
  apply StatMech.FrontierD.fkRectNatScale_squareDeckTranslation R n u

/--
[fkRectSquareRepresentativeVertex_dartTranslate_deck](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma fkRectSquareRepresentativeVertex_dartTranslate_deck_eq
  {R : FKRectTorus}
  {u : Int × Int}
  {d : FKRectIntegralSquareDart} :
-- imply
  fkRectSquareRepresentativeVertex R (fkRectIntegralSquareDartTranslate (fkRectSquareDeckTranslation R u) d).1 = fkRectSquareRepresentativeVertex R d.1 := by
-- proof
  apply StatMech.FrontierD.fkRectSquareRepresentativeVertex_dartTranslate_deck R u d

/--
[fkRectSquareRepresentativeVertex_dartTranslateEnd_deck](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma fkRectSquareRepresentativeVertex_dartTranslateEnd_deck_eq
  {R : FKRectTorus}
  {u : Int × Int}
  {d : FKRectIntegralSquareDart} :
-- imply
  fkRectSquareRepresentativeVertex R (fkRectIntegralSquareDartEnd (fkRectIntegralSquareDartTranslate (fkRectSquareDeckTranslation R u) d)) = fkRectSquareRepresentativeVertex R (fkRectIntegralSquareDartEnd d) := by
-- proof
  apply StatMech.FrontierD.fkRectSquareRepresentativeVertex_dartTranslateEnd_deck R u d

/--
[FKRectIntegralDartListSupportedOn.repeatTranslated_deck](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma repeatTranslated_deck_eq
  {R : FKRectTorus}
  {l : List FKRectIntegralSquareDart}
  {S : R.Vertex → Prop}
  {u : Int × Int}
  {n : Nat}
-- given
  (h : FKRectIntegralDartListSupportedOn R l S) :
-- imply
  FKRectIntegralDartListSupportedOn R (fkRectRepeatTranslatedDartPath l (fkRectSquareDeckTranslation R u) n) S := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralDartListSupportedOn.repeatTranslated_deck R u h n

/--
[FKRectIntegralDartListSupportedOn.exists_pointLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma exists_pointLift_eq
  {R : FKRectTorus}
  {l : List FKRectIntegralSquareDart}
  {S : R.Vertex → Prop}
  {p : ZMod (fkRectSquareCoverSide R) × ZMod (fkRectSquareCoverSide R)}
-- given
  (h : FKRectIntegralDartListSupportedOn R l S)
  (hp : FKRectDartListUsesPoint (l.map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide R))) p) :
-- imply
  ∃ z : Int × Int, fkRectIntegralSquarePointMod (fkRectSquareCoverSide R) z = p ∧ S (fkRectSquareRepresentativeVertex R z) := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralDartListSupportedOn.exists_pointLift R h hp

/--
[fkRectDartListUsesPoint_disjoint_of_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma fkRectDartListUsesPoint_disjoint_of_supported_eq
  {R : FKRectTorus}
  {l k : List FKRectIntegralSquareDart}
  {S T : R.Vertex → Prop}
-- given
  (hl : FKRectIntegralDartListSupportedOn R l S)
  (hk : FKRectIntegralDartListSupportedOn R k T)
  (hST : ∀ x, S x → ¬ T x) :
-- imply
  ∀ p, FKRectDartListUsesPoint (l.map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide R))) p → ¬ FKRectDartListUsesPoint (k.map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide R))) p := by
-- proof
  apply StatMech.FrontierD.fkRectDartListUsesPoint_disjoint_of_supported R hl hk hST

/--
[fkRectSquareCoverPointVertex_eq_of_pointMod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma fkRectSquareCoverPointVertex_eq_of_pointMod_eq
  {R : FKRectTorus}
  {z : Int × Int}
  {p : ZMod (fkRectSquareCoverSide R) × ZMod (fkRectSquareCoverSide R)}
-- given
  (h : fkRectIntegralSquarePointMod (fkRectSquareCoverSide R) z = p) :
-- imply
  fkRectSquareRepresentativeVertex R z = fkRectSquareCoverPointVertex R p := by
-- proof
  apply StatMech.FrontierD.fkRectSquareCoverPointVertex_eq_of_pointMod R z p h

/--
[FKRectIntegralSquareDartPath.exists_squareCoverDartWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma exists_squareCoverDartWitness_eq
  {R : FKRectTorus}
  {p u : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p (p.1 + u.1, p.2 + u.2) l) :
-- imply
  ∃ C : FKRectSquareCoverDartWitness R u, C.darts = (fkRectRepeatTranslatedDartPath l u (fkRectSquareCoverSide R)).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide R)) := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.exists_squareCoverDartWitness R h

/--
[FKRectSquareCoverDartWitness.not_independent_of_disjointSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma not_independent_of_disjointSupport_eq
  {R : FKRectTorus}
  {u v : Int × Int}
  {C : FKRectSquareCoverDartWitness R u}
  {D : FKRectSquareCoverDartWitness R v}
-- given
  (hdisj : ∀ p, FKRectDartListUsesPoint C.darts p → ¬ FKRectDartListUsesPoint D.darts p) :
-- imply
  ¬ FKRectWindingIndependent u v := by
-- proof
  apply StatMech.FrontierD.FKRectSquareCoverDartWitness.not_independent_of_disjointSupport C D hdisj

/--
[FKRectSquareWalkLift.not_windingIndependent_of_support_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma not_windingIndependent_of_support_disjoint_eq
  {R : FKRectTorus}
  {G H : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x x}
  {z : H.Walk y y}
  {p q a b : Int × Int}
-- given
  (hw : FKRectSquareWalkLift R w p q)
  (hz : FKRectSquareWalkLift R z a b)
  (hdisj : ∀ v, v ∈ w.support → v ∈ z.support → False) :
-- imply
  ¬ FKRectWindingIndependent (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.not_windingIndependent_of_support_disjoint R hw hz hdisj

/--
[fkRectClosedWalks_not_windingIndependent_of_support_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma fkRectClosedWalks_not_windingIndependent_of_support_disjoint_eq
  {R : FKRectTorus}
  {G H : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x x}
  {z : H.Walk y y}
-- given
  (hG : G ≤ fkRectTorusGraph R)
  (hH : H ≤ fkRectTorusGraph R)
  (hdisj : ∀ v, v ∈ w.support → v ∈ z.support → False) :
-- imply
  ¬ FKRectWindingIndependent (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
-- proof
  apply StatMech.FrontierD.fkRectClosedWalks_not_windingIndependent_of_support_disjoint R hG hH w z hdisj

/--
[fkRectClosedWalks_not_windingIndependent_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma fkRectClosedWalks_not_windingIndependent_of_not_reachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R omega).Walk x x}
  {z : (fkRectOpenGraph R omega).Walk y y}
-- given
  (hxy : ¬ (fkRectOpenGraph R omega).Reachable x y) :
-- imply
  ¬ FKRectWindingIndependent (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
-- proof
  apply StatMech.FrontierD.fkRectClosedWalks_not_windingIndependent_of_not_reachable R omega hxy w z

/--
[fkRectClosedWindingSubgroup_cross_dependent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma fkRectClosedWindingSubgroup_cross_dependent_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
-- given
  (hxy : ¬ (fkRectOpenGraph R omega).Reachable x y) :
-- imply
  ∀ u ∈ fkRectClosedWindingSubgroup R omega x, ∀ v ∈ fkRectClosedWindingSubgroup R omega y, ¬ FKRectWindingIndependent u v := by
-- proof
  apply StatMech.FrontierD.fkRectClosedWindingSubgroup_cross_dependent R omega hxy

/--
[not_windingIndependent_add_of_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma not_windingIndependent_add_of_pairwise_eq
  {a b c d : Int × Int}
-- given
  (hab : ¬ FKRectWindingIndependent a b)
  (had : ¬ FKRectWindingIndependent a d)
  (hbc : ¬ FKRectWindingIndependent b c)
  (hcd : ¬ FKRectWindingIndependent c d) :
-- imply
  ¬ FKRectWindingIndependent (a + c) (b + d) := by
-- proof
  apply StatMech.FrontierD.not_windingIndependent_add_of_pairwise a b c d hab had hbc hcd

/--
[windingSubgroup_sup_not_rankTwo_of_pairwise_dependent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean)
-/
@[path]
private lemma windingSubgroup_sup_not_rankTwo_of_pairwise_dependent_eq
  {H K : AddSubgroup (Int × Int)}
-- given
  (hH : ∀ a ∈ H, ∀ b ∈ H, ¬ FKRectWindingIndependent a b)
  (hK : ∀ a ∈ K, ∀ b ∈ K, ¬ FKRectWindingIndependent a b)
  (hHK : ∀ a ∈ H, ∀ b ∈ K, ¬ FKRectWindingIndependent a b) :
-- imply
  ¬ ∃ a ∈ H ⊔ K, ∃ b ∈ H ⊔ K, FKRectWindingIndependent a b := by
-- proof
  apply StatMech.FrontierD.windingSubgroup_sup_not_rankTwo_of_pairwise_dependent H K hH hK hHK


-- created on 2026-10-23
