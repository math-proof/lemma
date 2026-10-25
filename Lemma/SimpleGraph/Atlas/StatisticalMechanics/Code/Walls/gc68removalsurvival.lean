import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc68removalsurvival.Part2
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc68_K_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68_K_survives_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {K L D : Finset ι}
-- given
  (hDV : D ⊆ univ \ K) :
-- imply
  K ⊆ (K ∪ L) \ D := by
-- proof
  apply StatMech.Walls.gc68_K_survives hDV

/--
[gc68_ox_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68_ox_survives_eq
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
  apply StatMech.Walls.gc68_ox_survives ends hnd hox hKsrc hDV

/--
[gc68_xg_iff_og_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68_xg_iff_og_survives_eq
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
  apply StatMech.Walls.gc68_xg_iff_og_survives ends hnd hox hKsrc hDV

/--
[gc68_xg_survives_of_og](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68_xg_survives_of_og_eq
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
  (hDV : D ⊆ univ \ K)
  (hog : connK ends ((K ∪ L) \ D) o g) :
-- imply
  connK ends ((K ∪ L) \ D) x g := by
-- proof
  apply StatMech.Walls.gc68_xg_survives_of_og ends hnd hox hKsrc hDV hog

/--
[gc68b_xg_avoids_D_of_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68b_xg_avoids_D_of_disjointConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D P : Finset ι}
  {x g : W}
-- given
  (hPG : P ⊆ K ∪ L)
  (hPD : Disjoint P D)
  (hPconn : connK ends P x g) :
-- imply
  connK ends ((K ∪ L) \ D) x g := by
-- proof
  apply StatMech.Walls.gc68b_xg_avoids_D_of_disjointConnector ends hPG hPD hPconn

/--
[gc68b_xg_avoids_D_of_boundaryConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68b_xg_avoids_D_of_boundaryConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D P : Finset ι}
  {x g : W}
-- given
  (hPG : P ⊆ K ∪ L)
  (hPsrc : sources ends P = ({x, g} : Finset W))
  (hPD : Disjoint P D)
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hxg : x ≠ g) :
-- imply
  connK ends ((K ∪ L) \ D) x g := by
-- proof
  apply StatMech.Walls.gc68b_xg_avoids_D_of_boundaryConnector ends hPG hPsrc hPD hnd hxg

/--
[gc68_removalSurvival_of_ogReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68_removalSurvival_of_ogReroute_eq
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
  (h : gc68_OGReroute ends K o x y g) :
-- imply
  gc66_GDeg1RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc68_removalSurvival_of_ogReroute ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc h

/--
[gc68_gDeg1Connector_of_ogReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68_gDeg1Connector_of_ogReroute_eq
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
  (h : gc68_OGReroute ends K o x y g) :
-- imply
  gc65_GDeg1Connector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc68_gDeg1Connector_of_ogReroute ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc h

/--
[gc68_countIneq_of_ogReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68_countIneq_of_ogReroute_eq
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
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc68_OGReroute ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc68_countIneq_of_ogReroute ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc68_witness_og_via](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68_witness_og_via_eq
  {S : Finset (Fin 5)}
  {i : Fin 5}
-- given
  (hi : i ∈ S)
  (hi34 : i = 2 ∨ i = 3 ∨ i = 4) :
-- imply
  connK gc59_witnessEnds S 0 3 := by
-- proof
  apply StatMech.Walls.gc68_witness_og_via S hi hi34

/--
[gc68_witness_ogReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68_witness_ogReroute_eq :
-- imply
  gc68_OGReroute gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc68_witness_ogReroute

/--
[gc68_witness_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68_witness_removalSurvival_eq :
-- imply
  gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc68_witness_removalSurvival

/--
[gc68_witness_gDeg1Connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68_witness_gDeg1Connector_eq :
-- imply
  gc65_GDeg1Connector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc68_witness_gDeg1Connector

/--
[gc68_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean)
-/
@[path]
private lemma gc68_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K L D : Finset ι) (o x g : W), o ≠ x → sources ends K = ({o, x} : Finset W) → D ⊆ univ \ K → (connK ends ((K ∪ L) \ D) x g ↔ connK ends ((K ∪ L) \ D) o g)) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W), o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g → sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) → sources ends K = ({o, x} : Finset W) → gc68_OGReroute ends K o x y g → gc66_GDeg1RemovalSurvival ends K o x y g) ∧ gc68_OGReroute gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 ∧ gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 ∧ gc65_GDeg1Connector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc68_status


-- created on 2026-10-23
