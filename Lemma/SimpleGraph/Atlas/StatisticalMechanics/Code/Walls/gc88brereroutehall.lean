import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc88brereroutehall.Part5
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc88b_cogxgSet_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_cogxgSet_card_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  #(gc88b_cogxgSet ends m o x y g) = gc85b_pcount ends m {o, g} {x, g} := by
-- proof
  apply StatMech.Walls.gc88b_cogxgSet_card ends m o x y g

/--
[gc88b_T3Set_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_T3Set_card_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  #(gc88b_T3Set ends m o x y g) = gc87b_T3 ends m o x y g := by
-- proof
  apply StatMech.Walls.gc88b_T3Set_card ends m o x y g

/--
[gc88b_reroute_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_reroute_total_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
  {KK JJ : Finset ι × Finset ι}
-- given
  (hKK : KK ∈ gc88b_cogxgSet ends m o x y g)
  (hJJ : JJ ∈ gc88b_T3Set ends m o x y g) :
-- imply
  gc88b_reroute ends o g KK JJ := by
-- proof
  apply StatMech.Walls.gc88b_reroute_total ends m o x y g hKK hJJ

/--
[gc88b_nbr_eq_T3Set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_nbr_eq_T3Set_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
  {KK : Finset ι × Finset ι}
-- given
  (hKK : KK ∈ gc88b_cogxgSet ends m o x y g) :
-- imply
  gc88b_nbr ends m o x y g KK = gc88b_T3Set ends m o x y g := by
-- proof
  apply StatMech.Walls.gc88b_nbr_eq_T3Set ends m o x y g hKK

/--
[gc88b_biUnion_eq_T3Set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_biUnion_eq_T3Set_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
  {s : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}}
-- given
  (hs : s.Nonempty) :
-- imply
  s.biUnion (gc88b_hallFamily ends m o x y g) = gc88b_T3Set ends m o x y g := by
-- proof
  apply StatMech.Walls.gc88b_biUnion_eq_T3Set ends m o x y g hs

/--
[gc88b_marriage_iff_cogxg_le_T3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_marriage_iff_cogxg_le_T3_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc88b_Marriage ends m o x y g ↔ gc87b_CogxgLeT3 ends m o x y g := by
-- proof
  apply StatMech.Walls.gc88b_marriage_iff_cogxg_le_T3 ends m o x y g

/--
[gc88b_injection_of_marriage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_injection_of_marriage_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hM : gc88b_Marriage ends m o x y g) :
-- imply
  ∃ f : {KK // KK ∈ gc88b_cogxgSet ends m o x y g} → (Finset ι × Finset ι), Function.Injective f ∧ ∀ KK, f KK ∈ gc88b_hallFamily ends m o x y g KK := by
-- proof
  apply StatMech.Walls.gc88b_injection_of_marriage ends m o x y g hM

/--
[gc88b_cogxg_le_T3_of_marriage_via_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_cogxg_le_T3_of_marriage_via_hall_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hM : gc88b_Marriage ends m o x y g) :
-- imply
  gc87b_CogxgLeT3 ends m o x y g := by
-- proof
  apply StatMech.Walls.gc88b_cogxg_le_T3_of_marriage_via_hall ends m o x y g hM

/--
[gc88b_close_of_marriage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_close_of_marriage_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hM : gc88b_Marriage ends m o x y g) :
-- imply
  gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc88b_close_of_marriage ends m hnd hsrc hox hoy hog hM

/--
[gc88b_wred_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_wred_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  sources gc88b_wredEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc88b_wred_sources

/--
[gc88b_connK_color_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_connK_color_invariant_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {c : W → Bool}
  {a b : W}
-- given
  (hc : ∀ i ∈ K, ∀ a b : W, a ∈ ends i → b ∈ ends i → c a = c b)
  (h : connK ends K a b) :
-- imply
  c a = c b := by
-- proof
  apply StatMech.Walls.gc88b_connK_color_invariant ends K c hc h

/--
[gc88b_wred_cogxg_fibers_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_wred_cogxg_fibers_card_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  (((univ : Finset (Fin 4)).powerset.filter (fun K => sources gc88b_wredEnds K = ({0, 3} : Finset (Fin 4)))).filter (fun K₁ => connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ K₁) 1 3)) = ({{1}, {2}} : Finset (Finset (Fin 4))) := by
-- proof
  apply StatMech.Walls.gc88b_wred_cogxg_fibers_card

/--
[gc88b_wred_T3_fibers_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_wred_T3_fibers_card_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  (((univ : Finset (Fin 4)).powerset.filter (fun K => sources gc88b_wredEnds K = (∅ : Finset (Fin 4)))).filter (fun J₁ => connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 1 ∧ connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 2 ∧ connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 3)) = ({∅} : Finset (Finset (Fin 4))) := by
-- proof
  apply StatMech.Walls.gc88b_wred_T3_fibers_card

/--
[gc88b_wred_fiber_injection_impossible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_wred_fiber_injection_impossible_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  #(gc88b_cogxgSet gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3) = 2 ∧ #(gc88b_T3Set gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3) = gc87b_T3 gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 ∧ #(((univ : Finset (Fin 4)).powerset.filter (fun K => sources gc88b_wredEnds K = ({0, 3} : Finset (Fin 4)))).filter (fun K₁ => connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ K₁) 1 3)) > #(((univ : Finset (Fin 4)).powerset.filter (fun K => sources gc88b_wredEnds K = (∅ : Finset (Fin 4)))).filter (fun J₁ => connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 1 ∧ connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 2 ∧ connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 3)) := by
-- proof
  apply StatMech.Walls.gc88b_wred_fiber_injection_impossible

/--
[gc88b_tri_marriage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_tri_marriage_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc88b_Marriage gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc88b_tri_marriage

/--
[gc88b_hall_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_hall_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g) :
-- imply
  (∀ KK JJ, KK ∈ gc88b_cogxgSet ends m o x y g → JJ ∈ gc88b_T3Set ends m o x y g → gc88b_reroute ends o g KK JJ) ∧ (gc88b_Marriage ends m o x y g ↔ gc87b_CogxgLeT3 ends m o x y g) ∧ (gc88b_Marriage ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g) := by
-- proof
  apply StatMech.Walls.gc88b_hall_status ends m hnd hsrc hox hoy hog

/--
[gc88b_machine_findings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean)
-/
@[path]
private lemma gc88b_machine_findings_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gc88b_machine_findings


-- created on 2026-10-23
