import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc99consolidation
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc99_complete_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc99consolidation.lean)
-/
@[path]
private lemma gc99_complete_chain_eq
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
  (gc87b_CogxgLeT3 ends m o x y g → gc86b_CogxgResidual ends m o x y g) ∧ (gc86b_CogxgResidual ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g) ∧ (gc85b_ThreeCurrentBijection ends m o x y g ↔ gc85b_threeGapCount ends m o x y g ≤ 0) ∧ (gc87b_CogxgLeT3 ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g) := by
-- proof
  apply StatMech.Walls.gc99_complete_chain ends m hnd hsrc hox hoy hog

/--
[gc99_equivalent_residue_forms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc99consolidation.lean)
-/
@[path]
private lemma gc99_equivalent_residue_forms_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  (gc85b_ThreeCurrentBijection ends m o x y g ↔ gc85b_threeGapCount ends m o x y g ≤ 0) ∧ (gc85b_ThreeCurrentBijection ends m o x y g ↔ gc96b_SignedInvolution ends m o x y g) ∧ (gc85b_ThreeCurrentBijection ends m o x y g ↔ gc97b_PosNegReroute ends m o x y g) ∧ (gc96b_SignedInvolution ends m o x y g ↔ gc96b_signedPos ends m o x y g ≤ gc96b_signedNeg ends m o x y g) := by
-- proof
  apply StatMech.Walls.gc99_equivalent_residue_forms ends m o x y g

/--
[gc99_proved_fragments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc99consolidation.lean)
-/
@[path]
private lemma gc99_proved_fragments_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {R : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag)
  (hsrc : sources ends R = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g) :
-- imply
  (connK ends R o x ∨ connK ends R o y ∨ connK ends R o g) ∧ (∀ u v : W, u ≠ v → connK ends R u v → gc86b_ncount ends R {u, v} = gc86b_ncount ends R ∅) ∧ (gc85b_pcount ends R ∅ ∅ ≤ gc85b_pcount ends R ∅ {o, g} + gc85b_pcount ends R ∅ {o, x} + gc85b_pcount ends R ∅ {o, y}) ∧ (2 * (gc87b_T3 ends R o x y g : ℤ) ≤ gc87b_slack ends R o x y g) ∧ (∀ A B : Finset W, gc85b_pcount ends R A B = ∑ K₁ ∈ R.powerset.filter (fun K => sources ends K = A), gc86b_ncount ends (R \ K₁) B) ∧ gc96b_SignedInvolution gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc99_proved_fragments ends R hnd hsrc hox hoy hog

/--
[gc99_reroute_count_equality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc99consolidation.lean)
-/
@[path]
private lemma gc99_reroute_count_equality_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x g : W}
  {P : Finset ι}
-- given
  (hog : o ≠ g)
  (hPm : P ⊆ m)
  (hPsrc : sources ends P = {o, g}) :
-- imply
  #((m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P ∧ sources ends KK.1 = {o, g} ∧ sources ends KK.2 = ({x, g} : Finset W) ∆ {o, g})) = #((m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P ∧ sources ends KK.1 = {o, g} ∧ sources ends KK.2 = ({x, g} : Finset W))) := by
-- proof
  apply StatMech.Walls.gc99_reroute_count_equality ends m o x g hog P hPm hPsrc

/--
[gc99_refuted_routes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc99consolidation.lean)
-/
@[path]
private lemma gc99_refuted_routes_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  (¬ gc84b_GriffithsConsequence gc84b_ghsResidual) ∧ (∃ a b c r q p t : ℝ, gc27_TwoSourceGapFamily a b c r q p t ∧ ¬ (t + 2 * (a * b * c) ≤ a * p + b * q + c * r)) ∧ (∃ c00 c0og c0ox c0oy cogxg : ℤ, 0 ≤ c00 ∧ 0 ≤ c0og ∧ 0 ≤ c0ox ∧ 0 ≤ c0oy ∧ 0 ≤ cogxg ∧ cogxg ≤ c0og ∧ cogxg ≤ c0ox ∧ cogxg ≤ c0oy ∧ cogxg ≤ c00 ∧ ¬ (c00 + 2 * cogxg ≤ c0og + c0ox + c0oy)) ∧ (#(gc98b_cogRerouteImage gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3) < 2 * gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3}) ∧ (∃ (nS nT : ℕ) (adj : Fin nS → Fin nT → Prop), nS ≤ nT ∧ ∃ (fixedChoice : Fin nS → Fin nT), ¬ Function.Injective fixedChoice) := by
-- proof
  apply StatMech.Walls.gc99_refuted_routes

/--
[gc99_arithmetic_room_circular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc99consolidation.lean)
-/
@[path]
private lemma gc99_arithmetic_room_circular_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc98b_DisjointAccounting ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc99_arithmetic_room_circular ends m o x y g

/--
[gc99_minimal_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc99consolidation.lean)
-/
@[path]
private lemma gc99_minimal_residue_eq
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
  (hle : gc87b_CogxgLeT3 ends m o x y g) :
-- imply
  gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc99_minimal_residue ends m hnd hsrc hox hoy hog hle

/--
[gc99_residue_closes_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc99consolidation.lean)
-/
@[path]
private lemma gc99_residue_closes_ghs_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hres : ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc87b_CogxgLeT3 (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc99_residue_closes_ghs G β h hβ hh o x y hox hoy hxy hres hsupp

/--
[gc99_residue_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc99consolidation.lean)
-/
@[path]
private lemma gc99_residue_nonvacuous_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} = 1 ∧ gc87b_CogxgLeT3 gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc99_residue_nonvacuous

/--
[gc99_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc99consolidation.lean)
-/
@[path]
private lemma gc99_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (∀ {ι' : Type} [DecidableEq ι'] [Fintype ι'] (ends : ι' → Sym2 (Option V)) (m : Finset ι'), (∀ i ∈ m, ¬ (ends i).IsDiag) → sources ends m = ({some o, some x, some y, none} : Finset (Option V)) → gc87b_CogxgLeT3 ends m (some o) (some x) (some y) none → gc85b_ThreeCurrentBijection ends m (some o) (some x) (some y) none) ∧ (2 * (gc87b_T3 gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 : ℤ) ≤ gc87b_slack gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3) ∧ (¬ gc84b_GriffithsConsequence gc84b_ghsResidual) ∧ ((∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc87b_CogxgLeT3 (endsM (withGhost G) m) univ (some o) (some x) (some y) none) → gc82_ThreeGapAllConnSupported G β h o x y → eg_ursell3 G β h o x y ≤ 0) := by
-- proof
  apply StatMech.Walls.gc99_status G β h hβ hh o x y hox hoy hxy

/--
[gc99_consolidation_notes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc99consolidation.lean)
-/
@[path]
private lemma gc99_consolidation_notes_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gc99_consolidation_notes


-- created on 2026-10-23
