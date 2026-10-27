import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
open SimpleGraph StatMech StatMech.FrontierD


/--
[numClustersBC_le_sup_edge_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKBoundarySingleMerge.lean)
-/
@[path]
private lemma numClustersBC_le_sup_edge_add_one_eq
  [Fintype V]
  [DecidableEq V]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {x y : V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  FK.numClustersBC G C omega <= FK.numClustersBC G (C ⊔ SimpleGraph.edge x y) omega + 1 := by
-- proof
  apply StatMech.FrontierD.numClustersBC_le_sup_edge_add_one C x y omega

/--
[bcEventMass_sup_edge_le_q_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKBoundarySingleMerge.lean)
-/
@[path]
private lemma bcEventMass_sup_edge_le_q_mul_eq
  [Fintype V]
  [DecidableEq V]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {x y : V}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  FK.bcEventMass G (C ⊔ SimpleGraph.edge x y) p q A <= q * FK.bcEventMass G C p q A := by
-- proof
  apply StatMech.FrontierD.bcEventMass_sup_edge_le_q_mul C x y hp hp1 hq A

/--
[bcEventMass_add_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKBoundarySingleMerge.lean)
-/
@[path]
private lemma bcEventMass_add_compl_eq
  [Fintype V]
  [DecidableEq V]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.bcEventMass G C p q A + FK.bcEventMass G C p q Aᶜ = 1 := by
-- proof
  apply StatMech.FrontierD.bcEventMass_add_compl C hp hp1 hq A

/--
[bcEventMass_compl_le_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKBoundarySingleMerge.lean)
-/
@[path]
private lemma bcEventMass_compl_le_of_equiv_eq
  [Fintype V]
  [DecidableEq V]
  {C C' : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel C'.Adj]
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 V))}
  {D : ConfigSpace (Sym2 V) ≃ ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hfailure : ∀ omega, omega ∉ A → D omega ∈ A)
  (hprob : ∀ omega, FK.bcProb G C p q omega <= FK.bcProb G C' p q (D omega)) :
-- imply
  FK.bcEventMass G C p q Aᶜ <= FK.bcEventMass G C' p q A := by
-- proof
  apply StatMech.FrontierD.bcEventMass_compl_le_of_equiv C C' hp hp1 hq A D hfailure hprob

/--
[bcEventMass_ge_one_div_one_add_q_of_compl_le_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKBoundarySingleMerge.lean)
-/
@[path]
private lemma bcEventMass_ge_one_div_one_add_q_of_compl_le_sup_edge_eq
  [Fintype V]
  [DecidableEq V]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {x y : V}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hdual : FK.bcEventMass G C p q Aᶜ <= FK.bcEventMass G (C ⊔ SimpleGraph.edge x y) p q A) :
-- imply
  1 / (1 + q) <= FK.bcEventMass G C p q A := by
-- proof
  apply StatMech.FrontierD.bcEventMass_ge_one_div_one_add_q_of_compl_le_sup_edge C x y hp hp1 hq A hdual

/--
[bcEventMass_ge_one_div_one_add_mul_of_compl_le_mul_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKBoundarySingleMerge.lean)
-/
@[path]
private lemma bcEventMass_ge_one_div_one_add_mul_of_compl_le_mul_sup_edge_eq
  [Fintype V]
  [DecidableEq V]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {x y : V}
  {p q distortion : Real}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hdistortion : 0 <= distortion)
  (hdual : FK.bcEventMass G C p q Aᶜ <= distortion * FK.bcEventMass G (C ⊔ SimpleGraph.edge x y) p q A) :
-- imply
  1 / (1 + distortion * q) <= FK.bcEventMass G C p q A := by
-- proof
  apply StatMech.FrontierD.bcEventMass_ge_one_div_one_add_mul_of_compl_le_mul_sup_edge C x y hp hp1 hq hdistortion A hdual

/--
[bcEventMass_ge_one_div_one_add_q_of_dual_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKBoundarySingleMerge.lean)
-/
@[path]
private lemma bcEventMass_ge_one_div_one_add_q_of_dual_equiv_eq
  [Fintype V]
  [DecidableEq V]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {x y : V}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 V))}
  {D : ConfigSpace (Sym2 V) ≃ ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hfailure : ∀ omega, omega ∉ A → D omega ∈ A)
  (hprob : ∀ omega, FK.bcProb G C p q omega <= FK.bcProb G (C ⊔ SimpleGraph.edge x y) p q (D omega)) :
-- imply
  1 / (1 + q) <= FK.bcEventMass G C p q A := by
-- proof
  apply StatMech.FrontierD.bcEventMass_ge_one_div_one_add_q_of_dual_equiv C x y hp hp1 hq A D hfailure hprob

/--
[one_div_one_add_q_le_of_compl_le_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKBoundarySingleMerge.lean)
-/
@[path]
private lemma one_div_one_add_q_le_of_compl_le_merged_eq
  [Fintype V]
  [DecidableEq V]
  {q separate merged : Real}
-- given
  (hq : 1 <= q)
  (hcompl : 1 - separate <= merged)
  (hmerge : merged <= q * separate) :
-- imply
  1 / (1 + q) <= separate := by
-- proof
  apply StatMech.FrontierD.one_div_one_add_q_le_of_compl_le_merged hq hcompl hmerge

/--
[one_div_one_add_mul_le_of_compl_le_mul_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKBoundarySingleMerge.lean)
-/
@[path]
private lemma one_div_one_add_mul_le_of_compl_le_mul_merged_eq
  [Fintype V]
  [DecidableEq V]
  {q distortion separate merged : Real}
-- given
  (hq : 1 <= q)
  (hdistortion : 0 <= distortion)
  (hcompl : 1 - separate <= distortion * merged)
  (hmerge : merged <= q * separate) :
-- imply
  1 / (1 + distortion * q) <= separate := by
-- proof
  apply StatMech.FrontierD.one_div_one_add_mul_le_of_compl_le_mul_merged hq hdistortion hcompl hmerge


-- created on 2026-10-23
