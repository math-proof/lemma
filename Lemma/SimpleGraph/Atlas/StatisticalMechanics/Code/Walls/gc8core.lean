import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc8core.Part2
open Finset BigOperators SimpleGraph Set Classical StatMech StatMech.Walls


/--
[gc8_core_claim1_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_claim1_lower_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {y g : V}
  {eΛ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hgriff : Sharpness.expectationJ S β J ({y, g} : Finset V) ≤ eΛ) :
-- imply
  eΛ * Sharpness.currentSum S β J ({y, g} : Finset V) ≥ (Sharpness.expectationJ S β J ({y, g} : Finset V)) ^ 2 * Sharpness.currentSum S β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_core_claim1_lower_bound G S β J hβ hJ y g eΛ hgriff

/--
[gc8_core_claim1_eqclaim_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_claim1_eqclaim_lower_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {y g : V}
  {eΛ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hgriff : Sharpness.expectationJ S β J ({y, g} : Finset V) ≤ eΛ) :
-- imply
  eΛ * Sharpness.currentSum S β J ({y, g} : Finset V) ≥ (Sharpness.currentSum S β J ({y, g} : Finset V)) ^ 2 / Sharpness.currentSum S β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_core_claim1_eqclaim_lower_bound G S β J hβ hJ y g eΛ hgriff

/--
[gc8_core_claim1_eqclaim_lower_bound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_claim1_eqclaim_lower_bound_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {y g : V} :
-- imply
  0 ≤ (Sharpness.currentSum S β J ({y, g} : Finset V)) ^ 2 / Sharpness.currentSum S β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_core_claim1_eqclaim_lower_bound_nonneg G S β J y g

/--
[gc8_core_claim1_lower_bound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_claim1_lower_bound_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ (Sharpness.expectationJ S β J ({y, g} : Finset V)) ^ 2 * Sharpness.currentSum S β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_core_claim1_lower_bound_nonneg G S β J hβ hJ y g

/--
[gc8_core_claim1_normaliser_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_claim1_normaliser_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {GΛ GS : SimpleGraph V}
  [DecidableRel GΛ.Adj]
  [DecidableRel GS.Adj]
  {o x y g : V}
  {Jghost : Sym2 (Option V) → ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V)) * (isingExpectation GΛ β h (spinProd ({y} : Finset V))) ^ 2 * isingExpectation GS β h (spinProd ({o, x} : Finset V)) * (Sharpness.currentSum (withGhost GΛ) β Jghost ∅) ^ 2 := by
-- proof
  apply StatMech.Walls.gc8_core_claim1_normaliser_nonneg G GΛ GS β h hβ hh o x y g Jghost

/--
[gc8_core_delta_supported_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_delta_supported_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m) + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) := by
-- proof
  apply StatMech.Walls.gc8_core_delta_supported_allConn G ends F hox hoy hog hxy hxg hyg hnd hsrcSet

/--
[gc8_core_crossing_forces_oneCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_crossing_forces_oneCluster_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {o x y g w : V}
-- given
  (hox : connK ends K o x)
  (hyg : connK ends K y g)
  (hwo : connK ends K w o)
  (hwy : connK ends K w y) :
-- imply
  connK ends K o x ∧ connK ends K o y ∧ connK ends K o g := by
-- proof
  apply StatMech.Walls.gc8_core_crossing_forces_oneCluster G ends K hox hyg hwo hwy

/--
[gc8_core_delta_lower_bound_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_delta_lower_bound_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {A : Finset (Option V)}
  {eΛ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hgriff : Sharpness.expectationJ (withGhost G) β J A ≤ eΛ) :
-- imply
  eΛ * Sharpness.currentSum (withGhost G) β J A ≥ (Sharpness.expectationJ (withGhost G) β J A) ^ 2 * Sharpness.currentSum (withGhost G) β J ∅ ∧ 0 ≤ (Sharpness.expectationJ (withGhost G) β J A) ^ 2 * Sharpness.currentSum (withGhost G) β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_core_delta_lower_bound_ghost G β J A eΛ hβ hJ hgriff

/--
[gc8_core_delta_lower_bound_ghost_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_delta_lower_bound_ghost_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {A : Finset (Option V)}
  {eΛ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hgriff : Sharpness.expectationJ (withGhost G) β J A ≤ eΛ) :
-- imply
  0 ≤ eΛ * Sharpness.currentSum (withGhost G) β J A := by
-- proof
  apply StatMech.Walls.gc8_core_delta_lower_bound_ghost_nonneg G β J A eΛ hβ hJ hgriff

/--
[gc8_core_pairSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_pairSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {A : Finset V}
  {F : Finset ι → ℝ}
-- given
  (P : Finset ι → Prop)
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  0 ≤ drd_pairSum ends A F P := by
-- proof
  apply StatMech.Walls.gc8_core_pairSum_nonneg G ends A F P hF

/--
[gc8_core_delta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_delta_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hF : ∀ m, 0 ≤ F m)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) := by
-- proof
  apply StatMech.Walls.gc8_core_delta_nonneg G ends F hox hoy hog hxy hxg hyg hnd hF hsrcSet

/--
[gc8_pivotalBridge_of_eqSwi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_pivotalBridge_of_eqSwi_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hid : gc6_EqSwiIdentity G β h o) :
-- imply
  gc8_PivotalSignBridge G β h o := by
-- proof
  apply StatMech.Walls.gc8_pivotalBridge_of_eqSwi G β h hβ hh o hid

/--
[gc8_core_ursell_nonpos_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_ursell_nonpos_distinct_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {o : V}
  {x y : V}
-- given
  (β h : ℝ)
  (hbr : gc8_PivotalSignBridge G β h o)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc8_core_ursell_nonpos_distinct G β h o hbr x y hox hoy hxy

/--
[gc8_core_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_signDominance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {o : V}
-- given
  (β h : ℝ)
  (hbr : gc8_PivotalSignBridge G β h o) :
-- imply
  GHSSignDominance G β h o := by
-- proof
  apply StatMech.Walls.gc8_core_signDominance G β h o hbr

/--
[gc8_core_ursell_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_ursell_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {o : V}
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hbr : gc8_PivotalSignBridge G β h o) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc8_core_ursell_nonpos G β h hβ hh o hbr x y

/--
[gc8_core_ghs_concavity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_ghs_concavity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hbr : gc8_PivotalSignBridge G β h o) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc8_core_ghs_concavity G β h hβ hh o hbr

/--
[gc8_core_sharpness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_sharpness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {o : V}
  {Jc : ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hbr : gc8_PivotalSignBridge G β h o)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = Jc * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ Jc * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc8_core_sharpness G β h hβ hh o Jc hbr hfactor

/--
[gc8_core_bracket_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_bracket_surjective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {μ t : ℝ}
-- given
  (hμ : 0 ≤ μ)
  (hlo : -2 * μ ≤ t)
  (hhi : t ≤ 0) :
-- imply
  ∃ P : ℝ, 0 ≤ P ∧ P ≤ 1 ∧ -2 * μ * P = t := by
-- proof
  apply StatMech.Walls.gc8_core_bracket_surjective G hμ hlo hhi

/--
[gc8_core_pivotalBridge_iff_ursell_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_pivotalBridge_iff_ursell_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (∃ (D Z' : ℝ), (0 ≤ D) ∧ (0 < Z') ∧ eg_ursell3 G β h o x y * Z' = - D) ↔ eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc8_core_pivotalBridge_iff_ursell_nonpos G β h o x y hox hoy hxy

/--
[gc8_core_eqclaim_lower_bound_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_eqclaim_lower_bound_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι] :
-- imply
  0 ≤ (Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) 1 (fun _ => 1) ({1, 2} : Finset (Fin 4))) ^ 2 / Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) 1 (fun _ => 1) ∅ := by
-- proof
  apply StatMech.Walls.gc8_core_eqclaim_lower_bound_nonvacuous G

/--
[gc8_core_normaliser_nonneg_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_normaliser_nonneg_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι] :
-- imply
  0 ≤ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1, 2, 0} : Finset (Fin 3))) * (isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({2} : Finset (Fin 3)))) ^ 2 * isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3))) * (Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅) ^ 2 := by
-- proof
  apply StatMech.Walls.gc8_core_normaliser_nonneg_nonvacuous G

/--
[gc8_core_pivotalBridge_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_pivotalBridge_degenerate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hxy : x ≠ y) :
-- imply
  ∃ (D Z' : ℝ), (0 ≤ D) ∧ (0 < Z') ∧ eg_ursell3 G β h x x y * Z' = - D := by
-- proof
  apply StatMech.Walls.gc8_core_pivotalBridge_degenerate G β h hβ hh x y hxy

/--
[gc8_core_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean)
-/
@[path]
private lemma gc8_core_consistent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hid : gc6_EqSwiIdentity G β h o) :
-- imply
  gc8_PivotalSignBridge G β h o := by
-- proof
  apply StatMech.Walls.gc8_core_consistent G β h hβ hh o hid


-- created on 2026-10-23
