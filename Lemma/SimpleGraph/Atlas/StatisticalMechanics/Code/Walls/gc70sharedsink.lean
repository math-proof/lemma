import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc70sharedsink.Part3
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc70b_ogSurvival_of_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_ogSurvival_of_disjointConnector_eq
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
  apply StatMech.Walls.gc70b_ogSurvival_of_disjointConnector ends hPG hPD hPconn

/--
[gc70b_xgSurvival_of_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_xgSurvival_of_disjointConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D P : Finset ι}
  {o x g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hDV : D ⊆ univ \ K)
  (hPG : P ⊆ K ∪ L)
  (hPD : Disjoint P D)
  (hPconn : connK ends P o g) :
-- imply
  connK ends ((K ∪ L) \ D) x g := by
-- proof
  apply StatMech.Walls.gc70b_xgSurvival_of_disjointConnector ends hnd hox hKsrc hDV hPG hPD hPconn

/--
[gc70b_ogSurvival_of_ogConnAvoidingD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_ogSurvival_of_ogConnAvoidingD_eq
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
  (h : gc70b_OGConnAvoidingD ends K o x y g) :
-- imply
  gc69b_OGSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc70b_ogSurvival_of_ogConnAvoidingD ends hnd K hox hKsrc h

/--
[gc70b_ogConnAvoidingD_of_ogSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_ogConnAvoidingD_of_ogSurvival_eq
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
  (h : gc69b_OGSurvival ends K o x y g) :
-- imply
  gc70b_OGConnAvoidingD ends K o x y g := by
-- proof
  apply StatMech.Walls.gc70b_ogConnAvoidingD_of_ogSurvival ends hnd K hox hog hKsrc h

/--
[gc70b_ogConnAvoidingD_iff_ogSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_ogConnAvoidingD_iff_ogSurvival_eq
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
  gc70b_OGConnAvoidingD ends K o x y g ↔ gc69b_OGSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc70b_ogConnAvoidingD_iff_ogSurvival ends hnd K hox hog hKsrc

/--
[gc70b_countIneq_of_ogConnAvoidingD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_countIneq_of_ogConnAvoidingD_eq
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
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc70b_OGConnAvoidingD ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc70b_countIneq_of_ogConnAvoidingD ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc70b_sharedSink_disjoint_of_relConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_sharedSink_disjoint_of_relConn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {o g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g)
  (hconn : mngg_RelConn ends G o g 2) :
-- imply
  ∃ P₀ P₁ : Finset ι, P₀ ⊆ G ∧ P₁ ⊆ G ∧ Disjoint P₀ P₁ ∧ connK ends P₀ o g ∧ connK ends P₁ o g ∧ ∀ D : Finset ι, D ⊆ P₀ → connK ends (G \ D) o g := by
-- proof
  apply StatMech.Walls.gc70b_sharedSink_disjoint_of_relConn ends hnd hog hconn

/--
[gc70b_sharedSink_survival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_sharedSink_survival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G D P : Finset ι}
  {o g : W}
-- given
  (hPG : P ⊆ G)
  (hPD : Disjoint P D)
  (hPconn : connK ends P o g) :
-- imply
  connK ends (G \ D) o g := by
-- proof
  apply StatMech.Walls.gc70b_sharedSink_survival ends hPG hPD hPconn

/--
[gc70b_refutEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_refutEnds_loopless_eq :
-- imply
  ∀ i : Fin 4, ¬ (gc70b_refutEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc70b_refutEnds_loopless

/--
[gc70b_refut_isCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_refut_isCut_eq :
-- imply
  mngg_IsCut gc70b_refutEnds ({0, 1} : Finset (Fin 4)) 0 3 ({1} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc70b_refut_isCut

/--
[gc70b_superSource_route_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_superSource_route_refuted_eq :
-- imply
  ¬ mngg_RelConn gc70b_refutEnds ({0, 1} : Finset (Fin 4)) 0 3 2 := by
-- proof
  apply StatMech.Walls.gc70b_superSource_route_refuted

/--
[gc70b_witness_P3_src](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_witness_P3_src_eq :
-- imply
  sources gc59_witnessEnds ({3} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc70b_witness_P3_src

/--
[gc70b_witness_P4_src](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_witness_P4_src_eq :
-- imply
  sources gc59_witnessEnds ({4} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc70b_witness_P4_src

/--
[gc70b_witness_P3_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_witness_P3_conn_eq :
-- imply
  connK gc59_witnessEnds ({3} : Finset (Fin 5)) 0 3 := by
-- proof
  apply StatMech.Walls.gc70b_witness_P3_conn

/--
[gc70b_witness_P4_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_witness_P4_conn_eq :
-- imply
  connK gc59_witnessEnds ({4} : Finset (Fin 5)) 0 3 := by
-- proof
  apply StatMech.Walls.gc70b_witness_P4_conn

/--
[gc70b_witness_ogConnAvoidingD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_witness_ogConnAvoidingD_eq :
-- imply
  gc70b_OGConnAvoidingD gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc70b_witness_ogConnAvoidingD

/--
[gc70b_witness_ogSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_witness_ogSurvival_eq :
-- imply
  gc69b_OGSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc70b_witness_ogSurvival

/--
[gc70b_witness_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_witness_removalSurvival_eq :
-- imply
  gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc70b_witness_removalSurvival

/--
[gc70b_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean)
-/
@[path]
private lemma gc70b_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W), o ≠ x → o ≠ g → sources ends K = ({o, x} : Finset W) → (gc70b_OGConnAvoidingD ends K o x y g ↔ gc69b_OGSurvival ends K o x y g)) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (o x y g : W), o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g → sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) → (∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc70b_OGConnAvoidingD ends K o x y g) → gc39_ThreeColouringCountIneq ends o x y g) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (G : Finset ι) (o g : W), o ≠ g → mngg_RelConn ends G o g 2 → ∃ P₀ P₁ : Finset ι, P₀ ⊆ G ∧ P₁ ⊆ G ∧ Disjoint P₀ P₁ ∧ connK ends P₀ o g ∧ connK ends P₁ o g ∧ ∀ D : Finset ι, D ⊆ P₀ → connK ends (G \ D) o g) ∧ (¬ mngg_RelConn gc70b_refutEnds ({0, 1} : Finset (Fin 4)) 0 3 2) ∧ gc70b_OGConnAvoidingD gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 ∧ gc69b_OGSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 ∧ gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc70b_status


-- created on 2026-10-23
