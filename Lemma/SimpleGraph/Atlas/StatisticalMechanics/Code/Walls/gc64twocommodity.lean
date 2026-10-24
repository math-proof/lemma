import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc64twocommodity
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc64_disjointConnector_of_fixedD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_disjointConnector_of_fixedD_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (h : gc64_SharedSinkFixedD ends K o x y g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc64_disjointConnector_of_fixedD ends K h

/--
[gc64_sharedSinkFixedD_of_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_sharedSinkFixedD_of_disjointConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (h : gc57_DisjointConnector ends K o x y g) :
-- imply
  gc64_SharedSinkFixedD ends K o x y g := by
-- proof
  apply StatMech.Walls.gc64_sharedSinkFixedD_of_disjointConnector ends K h

/--
[gc64_sharedSinkFixedD_iff_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_sharedSinkFixedD_iff_disjointConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W} :
-- imply
  gc64_SharedSinkFixedD ends K o x y g ↔ gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc64_sharedSinkFixedD_iff_disjointConnector ends K

/--
[gc64_two_disjoint_from_g](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_two_disjoint_from_g_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {g a : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hne : g ≠ a)
  (hga : connK ends G g a)
  (hga2 : ∀ P₁ : Finset ι, P₁ ⊆ G → sources ends P₁ = ({g, a} : Finset W) → connK ends (G \ P₁) g a) :
-- imply
  ∃ P₁ P₂ : Finset ι, P₁ ⊆ G ∧ P₂ ⊆ G ∧ Disjoint P₁ P₂ ∧ sources ends P₁ = ({g, a} : Finset W) ∧ sources ends P₂ = ({g, a} : Finset W) ∧ connK ends P₁ g a ∧ connK ends P₂ g a := by
-- proof
  apply StatMech.Walls.gc64_two_disjoint_from_g ends hnd hne hga hga2

/--
[gc64_relative2_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_relative2_survives_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G P₁ P₂ D : Finset ι}
  {x g : W}
-- given
  (hP₂G : P₂ ⊆ G)
  (hdisj : Disjoint P₁ P₂)
  (hDP₁ : D ⊆ P₁)
  (hP₂c : connK ends P₂ x g) :
-- imply
  connK ends (G \ D) x g := by
-- proof
  apply StatMech.Walls.gc64_relative2_survives ends hP₂G hdisj hDP₁ hP₂c

/--
[gc64_disjointConnector_of_commonRel2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_disjointConnector_of_commonRel2_eq
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
  (hxg : x ≠ g)
  (hDV : D ⊆ univ \ K)
  (hDsrc : sources ends D = ({y, g} : Finset W))
  (hrel2 : ∀ L ∈ gc51_LblockSet ends K o x g, ∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ D ∩ (K ∪ L) ⊆ P₁ ∧ sources ends P₁ = ({x, g} : Finset W) ∧ connK ends ((K ∪ L) \ P₁) x g) :
-- imply
  gc64_SharedSinkFixedD ends K o x y g := by
-- proof
  apply StatMech.Walls.gc64_disjointConnector_of_commonRel2 ends hnd K hxg hDV hDsrc hrel2

/--
[gc64_countIneq_of_sharedSinkFixedD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_countIneq_of_sharedSinkFixedD_eq
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
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc64_SharedSinkFixedD ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc64_countIneq_of_sharedSinkFixedD ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc64_sharedSinkFixedD_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_sharedSinkFixedD_of_disjoint_eq
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
  (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) :
-- imply
  gc64_SharedSinkFixedD ends K o x y g := by
-- proof
  apply StatMech.Walls.gc64_sharedSinkFixedD_of_disjoint ends K hDV hDsrc hdisj

/--
[gc64_sharedSinkFixedD_of_gDegOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_sharedSinkFixedD_of_gDegOne_eq
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
  (hg1 : degK ends (univ : Finset ι) g = 1) :
-- imply
  gc64_SharedSinkFixedD ends K o x y g := by
-- proof
  apply StatMech.Walls.gc64_sharedSinkFixedD_of_gDegOne ends hnd K hoy hog hxy hxg hyg huniv hKsrc hg1

/--
[gc64_disjointConnector_of_gDegOne'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_disjointConnector_of_gDegOne'_eq
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
  (hg1 : degK ends (univ : Finset ι) g = 1) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc64_disjointConnector_of_gDegOne' ends hnd K hoy hog hxy hxg hyg huniv hKsrc hg1

/--
[gc64_witness_sharedSinkFixedD_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_witness_sharedSinkFixedD_K13_eq :
-- imply
  gc64_SharedSinkFixedD gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc64_witness_sharedSinkFixedD_K13

/--
[gc64_witness_sharedSinkFixedD_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_witness_sharedSinkFixedD_K23_eq :
-- imply
  gc64_SharedSinkFixedD gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc64_witness_sharedSinkFixedD_K23

/--
[gc64_witness_cosetGateDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_witness_cosetGateDom_eq :
-- imply
  gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc64_witness_cosetGateDom

/--
[gc64_refut_sharedSinkFixedD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_refut_sharedSinkFixedD_eq :
-- imply
  gc64_SharedSinkFixedD gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc64_refut_sharedSinkFixedD

/--
[gc64_refut_sharedSink_beats_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_refut_sharedSink_beats_reroute_eq :
-- imply
  (¬ gc59_RerouteConnector gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3) ∧ gc64_SharedSinkFixedD gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc64_refut_sharedSink_beats_reroute

/--
[gc64_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc64twocommodity.lean)
-/
@[path]
private lemma gc64_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W), gc64_SharedSinkFixedD ends K o x y g ↔ gc57_DisjointConnector ends K o x y g) ∧ gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 ∧ (¬ gc59_RerouteConnector gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3) ∧ gc64_SharedSinkFixedD gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc64_status


-- created on 2026-10-23
