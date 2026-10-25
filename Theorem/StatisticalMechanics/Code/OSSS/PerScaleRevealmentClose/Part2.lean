/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.PrefixCoversClose.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKRevealmentClose
import Def.StatisticalMechanics.Code.OSSS.PerScaleRevealmentClose
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace PerScaleRevealmentClose

open OSSS.Coding

open OSSS.AdaptMConditional

open StatMech.OSSS

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.ReachDomination

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.PrefixCoversClose

open StatMech.OSSS.FKRevealmentClose

open StatMech.OSSS.MonotonicFK

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


section LatticeResidue

variable {d : ℕ}


theorem psr_perScale_of_familyFrontierConn {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {κ : Type*} {nE : ℕ} (σf : κ → (Fin nE ≃ E))
    (f : ConfigSpace E → ℝ)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (kscale : κ → ℕ)
    [∀ k e X, Decidable (ConnOpenSet endU endV X (endU e) (vertexBoundary d (kscale k)))]
    [∀ k e X, Decidable (ConnOpenSet endU endV X (endV e) (vertexBoundary d (kscale k)))]
    [∀ k e X, Decidable (ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d (kscale k)))]
    [∀ k e X, Decidable (ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d (kscale k)))]
    (hfront : psr_FamilyFrontierConn σf f endU endV (fun k => vertexBoundary d (kscale k))) :
    ∀ (k : κ) (e : E),
      revealAdapt μ (σf k) f e
        ≤ Lindeberg.mean μ
            (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d (kscale k))
                      then (1 : ℝ) else 0)
          + Lindeberg.mean μ
            (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d (kscale k))
                      then (1 : ℝ) else 0) :=
  fun k e =>
    revealAdapt_le_connBox hpos hμ1 (σf k) f hinj hcoh hadj (kscale k) e (hfront k e)

end LatticeResidue


section FKResidue

variable {W : Type*} [Fintype W] [DecidableEq W]


theorem psr_fk_q2_cov_lower_bound_of_perScale
    (G : SimpleGraph W) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {κ : Type*} [Fintype κ] [Nonempty κ] {nE : ℕ} (σf : κ → (Fin nE ≃ Sym2 W))
    {f : ConfigSpace (Sym2 W) → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hidem : ∀ ω, f ω * f ω = f ω)
    (R : κ → Sym2 W → ℝ) (D : ℝ) (hDpos : 0 < D)
    (hreach : ∀ k e, revealAdapt (fkMass G p 2) (σf k) f e ≤ R k e)
    (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
    Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) / D
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) :=
  FKRevealmentClose.fk_q2_cov_lower_bound_from_perScaleReveal G hp hp1 σf hf hf0 hf1 hidem
    R D hDpos hreach hsum

end FKResidue


theorem psr_familyFrontierConn_univ {κ : Type*} {nE : ℕ} (σf : κ → (Fin nE ≃ E))
    (f : ConfigSpace E → ℝ) (endU endV : E → V) :
    psr_FamilyFrontierConn σf f endU endV (fun _ => (Set.univ : Set V)) :=
  fun k e => frontierConn_univ (σf k) f endU endV e


theorem psr_reachOpen_allClosed {endU endV : E → V} {x y : V}
    (h : ReachOpen endU endV (fun _ => false) x y) : x = y := by
  induction h with
  | refl x => rfl
  | step e hopen _ _ _ => simp at hopen


end PerScaleRevealmentClose
end OSSS
end StatMech
