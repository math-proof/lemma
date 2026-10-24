import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc2_codinglawjoint
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc2_integrable_g_codeMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawjoint.lean)
-/
@[path]
private lemma oc2_integrable_g_codeMap_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ} :
-- imply
  Integrable (fun u : Fin n → ℝ => g (codeMap μ (σ : Fin n → E) u)) (Vcube n) := by
-- proof
  apply StatMech.Walls.oc2_integrable_g_codeMap μ σ g

/--
[oc2_codingLawJoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawjoint.lean)
-/
@[path]
private lemma oc2_codingLawJoint_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (h : ConfigSpace E → ConfigSpace E → ℝ) :
-- imply
  ∫ p, h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2) ∂((Vcube n).prod (Vcube n)) = ∑ x, ∑ y, h x y * μ x * μ y := by
-- proof
  apply StatMech.Walls.oc2_codingLawJoint μ hpos hμ1 σ h

/--
[oc2_Wt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawjoint.lean)
-/
@[path]
private lemma oc2_Wt_zero_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ} :
-- imply
  Wt U V 0 = U := by
-- proof
  apply StatMech.Walls.oc2_Wt_zero U V

/--
[oc2_Wt_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawjoint.lean)
-/
@[path]
private lemma oc2_Wt_full_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ} :
-- imply
  Wt U V n = V := by
-- proof
  apply StatMech.Walls.oc2_Wt_full U V

/--
[oc2_codingLawJoint_interp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawjoint.lean)
-/
@[path]
private lemma oc2_codingLawJoint_interp_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (h : ConfigSpace E → ConfigSpace E → ℝ) :
-- imply
  ∫ p, h (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 0)) (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 n)) ∂((Vcube n).prod (Vcube n)) = ∑ x, ∑ y, h x y * μ x * μ y := by
-- proof
  apply StatMech.Walls.oc2_codingLawJoint_interp μ hpos hμ1 σ h

/--
[oc2_codingLawJoint_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawjoint.lean)
-/
@[path]
private lemma oc2_codingLawJoint_factor_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (h : ConfigSpace E → ConfigSpace E → ℝ) :
-- imply
  ∫ p, h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2) ∂((Vcube n).prod (Vcube n)) = ∑ x, (∑ y, h x y * μ y) * μ x := by
-- proof
  apply StatMech.Walls.oc2_codingLawJoint_factor μ hpos hμ1 σ h

/--
[oc2_codingLawJoint_marginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawjoint.lean)
-/
@[path]
private lemma oc2_codingLawJoint_marginal_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {a b : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∫ p, a (codeMap μ (σ : Fin n → E) p.1) * b (codeMap μ (σ : Fin n → E) p.2) ∂((Vcube n).prod (Vcube n)) = (∑ x, a x * μ x) * (∑ y, b y * μ y) := by
-- proof
  apply StatMech.Walls.oc2_codingLawJoint_marginal μ hpos hμ1 σ a b

/--
[oc2_fk_codingLawJoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_codinglawjoint.lean)
-/
@[path]
private lemma oc2_fk_codingLawJoint_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (h : ConfigSpace (Sym2 V) → ConfigSpace (Sym2 V) → ℝ) :
-- imply
  ∫ pr, h (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) pr.1) (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) pr.2) ∂((Vcube n).prod (Vcube n)) = ∑ x, ∑ y, h x y * fkMass G p q x * fkMass G p q y := by
-- proof
  apply StatMech.Walls.oc2_fk_codingLawJoint G hp hp1 hq σ h


-- created on 2026-10-23
