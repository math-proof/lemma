import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc16_tpsum_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_tpsum_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥S.edgeFinset → ℕ}
  {A B : Finset V} :
-- imply
  gc15_tpsum S β J m A B = gc15_tpsum S β J m B A := by
-- proof
  apply StatMech.Walls.gc16_tpsum_symm G S β J m A B

/--
[gc16_tpsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_tpsum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥S.edgeFinset → ℕ}
  {A B : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ gc15_tpsum S β J m A B := by
-- proof
  apply StatMech.Walls.gc16_tpsum_nonneg G S β J hβ hJ m A B

/--
[gc16_tFiber_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_tFiber_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B C : Finset V}
  {m : ↥S.edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ gc15_tFiber S β J A B C m := by
-- proof
  apply StatMech.Walls.gc16_tFiber_nonneg G S β J hβ hJ A B C m

/--
[gc16_inner_eq_splitWeightedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_inner_eq_splitWeightedSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {p : ↥S.edgeFinset → ℕ}
  {A : Finset V} :
-- imply
  (∑ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ p e}, (if sources S (ofEdgeFun S K₁.1) = A then weight S β J (ofEdgeFun S K₁.1) else 0) * weight S β J (ofEdgeFun S (fun e => p e - K₁.1 e))) = splitWeightedSum S β J (ofEdgeFun S p) 1 A := by
-- proof
  apply StatMech.Walls.gc16_inner_eq_splitWeightedSum G S β J p A

/--
[gc16_tpsum_eq_sigma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_tpsum_eq_sigma_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥S.edgeFinset → ℕ}
  {A B : Finset V} :
-- imply
  gc15_tpsum S β J m A B = ∑ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e}, (if sources S (ofEdgeFun S K₂.1) = B then weight S β J (ofEdgeFun S K₂.1) else 0) * (∑ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e - K₂.1 e}, (if sources S (ofEdgeFun S K₁.1) = A then weight S β J (ofEdgeFun S K₁.1) else 0) * weight S β J (ofEdgeFun S (fun e => (m e - K₂.1 e) - K₁.1 e))) := by
-- proof
  apply StatMech.Walls.gc16_tpsum_eq_sigma G S β J m A B

/--
[gc16_tpsum_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_tpsum_bridge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥S.edgeFinset → ℕ}
  {A B : Finset V} :
-- imply
  gc15_tpsum S β J m A B = ∑ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e}, (if sources S (ofEdgeFun S K₂.1) = B then weight S β J (ofEdgeFun S K₂.1) else 0) * splitWeightedSum S β J (ofEdgeFun S (fun e => m e - K₂.1 e)) 1 A := by
-- proof
  apply StatMech.Walls.gc16_tpsum_bridge G S β J m A B

/--
[gc16_threeGap_eq_gated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_threeGap_eq_gated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  gc15_threeGap G β h o x y m = gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none} := by
-- proof
  apply StatMech.Walls.gc16_threeGap_eq_gated G S β h o x y hox hoy hxy m hm

/--
[gc16_perConfig_off_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_perConfig_off_boundary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m) ≠ ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  gc15_threeGap G β h o x y m ≤ 0 := by
-- proof
  apply StatMech.Walls.gc16_perConfig_off_boundary G S β h o x y hox hoy hxy m hm

/--
[gc16_perConfigSign_of_cert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_perConfigSign_of_cert_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcert : gc16_PerConfigCert G β h o x y) :
-- imply
  gc15_PerConfigUrsellSign G β h o x y := by
-- proof
  apply StatMech.Walls.gc16_perConfigSign_of_cert G S β h o x y hox hoy hxy hcert

/--
[gc16_cert_closes_u3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_cert_closes_u3_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcert : gc16_PerConfigCert G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc16_cert_closes_u3 G S β h o x y hox hoy hxy hcert

/--
[gc16_ghs_of_cert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_ghs_of_cert_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hcert : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc16_PerConfigCert G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc16_ghs_of_cert G S β h hβ hh o hcert

/--
[gc16_aizenman_barsky_of_cert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_aizenman_barsky_of_cert_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o : V}
  {J : ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hcert : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc16_PerConfigCert G β h o x y)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc16_aizenman_barsky_of_cert G S β h hβ hh o J hcert hfactor

/--
[gc16_cert_of_perConfigSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_cert_of_perConfigSign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hsign : gc15_PerConfigUrsellSign G β h o x y) :
-- imply
  gc16_PerConfigCert G β h o x y := by
-- proof
  apply StatMech.Walls.gc16_cert_of_perConfigSign G S β h o x y hox hoy hxy hsign

/--
[gc16_cert_iff_perConfigSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean)
-/
@[path]
private lemma gc16_cert_iff_perConfigSign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc16_PerConfigCert G β h o x y ↔ gc15_PerConfigUrsellSign G β h o x y := by
-- proof
  apply StatMech.Walls.gc16_cert_iff_perConfigSign G S β h o x y hox hoy hxy


-- created on 2026-10-23
