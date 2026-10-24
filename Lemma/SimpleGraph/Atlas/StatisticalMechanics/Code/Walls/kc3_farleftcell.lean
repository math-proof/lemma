import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc3_farleftcell
open Set SimpleGraph StatMech StatMech.Walls


/--
[kc3_exists_farLeft_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_farleftcell.lean)
-/
@[path]
private lemma kc3_exists_farLeft_notMem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K F : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hF : F.Finite) :
-- imply
  ∃ q : Site 2, (∀ p ∈ F, q 0 ≤ p 0) ∧ q ∉ K := by
-- proof
  apply StatMech.Walls.kc3_exists_farLeft_notMem hK hF

/--
[kc3_exists_farLeft_orbitLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_farleftcell.lean)
-/
@[path]
private lemma kc3_exists_farLeft_orbitLoop_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  ∃ q : Site 2, (∀ p ∈ (mpl_orbitLoop K a).support, q 0 ≤ p 0) ∧ q ∉ K := by
-- proof
  apply StatMech.Walls.kc3_exists_farLeft_orbitLoop a hK

/--
[kc3_exists_farLeft_clusterOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_farleftcell.lean)
-/
@[path]
private lemma kc3_exists_farLeft_clusterOrigin_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : {e : Dart // IsBoundaryDart (cluster 2 ω (origin 2)) e}}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ∃ q : Site 2, (∀ p ∈ (mpl_orbitLoop (cluster 2 ω (origin 2)) a).support, q 0 ≤ p 0) ∧ q ∉ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Walls.kc3_exists_farLeft_clusterOrigin hfin a

/--
[kc3_farLeft_rayCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_farleftcell.lean)
-/
@[path]
private lemma kc3_farLeft_rayCount_zero_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {q : Site 2}
-- given
  (hq : ∀ p ∈ (mpl_orbitLoop K a).support, q 0 ≤ p 0) :
-- imply
  jec_rayCount q (mpl_orbitLoop K a) = 0 := by
-- proof
  apply StatMech.Walls.kc3_farLeft_rayCount_zero a hq

/--
[kc3_farLeft_notMem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_farleftcell.lean)
-/
@[path]
private lemma kc3_farLeft_notMem_leftRegion_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {q : Site 2}
-- given
  (hq : ∀ p ∈ (mpl_orbitLoop K a).support, q 0 ≤ p 0) :
-- imply
  q ∉ jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc3_farLeft_notMem_leftRegion a hq

/--
[kc3_escapeWalk_base_farLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_farleftcell.lean)
-/
@[path]
private lemma kc3_escapeWalk_base_farLeft_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hoff : exc_OffSupportReachesExterior K a)
  (hzK : z ∉ K)
  (hzsupp : z ∉ (mpl_orbitLoop K a).support) :
-- imply
  ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) ∧ jec_rayCount z0 (mpl_orbitLoop K a) = 0 := by
-- proof
  apply StatMech.Walls.kc3_escapeWalk_base_farLeft K a hoff hzK hzsupp


-- created on 2026-10-23
