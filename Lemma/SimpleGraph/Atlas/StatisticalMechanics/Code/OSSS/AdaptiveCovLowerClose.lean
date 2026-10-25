import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCovLowerClose
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptiveCovLowerClose


/--
[acl_fk_q2_hcov_crossTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCovLowerClose.lean)
-/
@[path]
private lemma acl_fk_q2_hcov_crossTree_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {p : ℝ}
  {edge : Sym2 W → Sym2 (Site d)}
  {endU endV : Sym2 W → Site d}
  {o : Site d}
  {l : List (Sym2 W)}
  {disc₀ : ℕ → Finset (Site d)}
  {n : ℕ}
  {D : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hl : ∀ e, e ∈ l)
  (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
  (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
  (hoB : ∀ k, o ∉ disc₀ k)
  (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
  (hn : 1 ≤ n)
  (hDpos : 0 < D)
  (hsum : ∀ e : Sym2 W, (∑ k : ↥(Finset.Icc 1 n), boxReveal (fkMass G p 2) edge endU endV (k : ℕ) e) ≤ (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) * D) :
-- imply
  Lindeberg.mean (fkMass G p 2) (crossInd edge o n) * (1 - Lindeberg.mean (fkMass G p 2) (crossInd edge o n)) / D ≤ ∑ e, Lindeberg.cov (fkMass G p 2) (crossInd edge o n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptiveCovLowerClose.acl_fk_q2_hcov_crossTree G hp hp1 hinj hcoh hadj o l hl disc₀ hdisc₀sub hdisc₀sup hoB ho n hn D hDpos hsum

/--
[acl_boxReveal_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCovLowerClose.lean)
-/
@[path]
private lemma acl_boxReveal_sum_le_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {μ : ConfigSpace (Sym2 W) → ℝ}
  {edge : Sym2 W → Sym2 (Site d)}
  {endU endV : Sym2 W → Site d}
  {n : ℕ}
  {Λ : Finset (Site d)}
  {conn : Site d → ℕ → ℝ}
  {e : Sym2 W}
  {ru rv : ℕ}
-- given
  (hne : Λ.Nonempty)
  (hconnnn : ∀ x j, 0 ≤ conn x j)
  (hru : ru ≤ n)
  (hrv : rv ≤ n)
  (hu : endU e ∈ Λ)
  (hv : endV e ∈ Λ)
  (hcompu : ∀ k, Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ conn (endU e) ((k : ℤ) - (ru : ℤ)).natAbs)
  (hcompv : ∀ k, Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ conn (endV e) ((k : ℤ) - (rv : ℤ)).natAbs) :
-- imply
  (∑ k : ↥(Finset.Icc 1 n), boxReveal μ edge endU endV (k : ℕ) e) ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), conn x j) := by
-- proof
  apply StatMech.OSSS.AdaptiveCovLowerClose.acl_boxReveal_sum_le n Λ hne conn hconnnn e ru rv hru hrv hu hv hcompu hcompv

/--
[acl_fk_q2_hcov_of_translationComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCovLowerClose.lean)
-/
@[path]
private lemma acl_fk_q2_hcov_of_translationComparison_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {p : ℝ}
  {edge : Sym2 W → Sym2 (Site d)}
  {endU endV : Sym2 W → Site d}
  {o : Site d}
  {l : List (Sym2 W)}
  {disc₀ : ℕ → Finset (Site d)}
  {n : ℕ}
  {Λ : Finset (Site d)}
  {conn : Site d → ℕ → ℝ}
  {rdist : Sym2 W → ℕ × ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hl : ∀ e, e ∈ l)
  (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
  (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
  (hoB : ∀ k, o ∉ disc₀ k)
  (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
  (hn : 1 ≤ n)
  (hne : Λ.Nonempty)
  (hconnnn : ∀ x j, 0 ≤ conn x j)
  (hLu : ∀ e : Sym2 W, endU e ∈ Λ)
  (hLv : ∀ e : Sym2 W, endV e ∈ Λ)
  (hru : ∀ e : Sym2 W, (rdist e).1 ≤ n)
  (hrv : ∀ e : Sym2 W, (rdist e).2 ≤ n)
  (hcomp : ∀ (e : Sym2 W), (∀ k, Lindeberg.mean (fkMass G p 2) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ conn (endU e) ((k : ℤ) - ((rdist e).1 : ℤ)).natAbs) ∧ (∀ k, Lindeberg.mean (fkMass G p 2) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ conn (endV e) ((k : ℤ) - ((rdist e).2 : ℤ)).natAbs))
  (hmaxpos : 0 < Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), conn x j)) :
-- imply
  Lindeberg.mean (fkMass G p 2) (crossInd edge o n) * (1 - Lindeberg.mean (fkMass G p 2) (crossInd edge o n)) / (4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), conn x j) / (n : ℝ)) ≤ ∑ e, Lindeberg.cov (fkMass G p 2) (crossInd edge o n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptiveCovLowerClose.acl_fk_q2_hcov_of_translationComparison G hp hp1 hinj hcoh hadj o l hl disc₀ hdisc₀sub hdisc₀sup hoB ho n hn Λ hne conn hconnnn hLu hLv rdist hru hrv hcomp hmaxpos

/--
[acl_fk_q2_poincare_adaptive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCovLowerClose.lean)
-/
@[path]
private lemma acl_fk_q2_poincare_adaptive_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {p : ℝ}
  {edge : Sym2 W → Sym2 (Site d)}
  {endU endV : Sym2 W → Site d}
  {o : Site d}
  {l : List (Sym2 W)}
  {disc₀ : ℕ → Finset (Site d)}
  {n : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hl : ∀ e, e ∈ l)
  (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
  (hoB : ∀ k, o ∉ disc₀ k)
  (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
  (hn : 1 ≤ n) :
-- imply
  Lindeberg.var (fkMass G p 2) (crossInd edge o n) ≤ ∑ e, Lindeberg.cov (fkMass G p 2) (crossInd edge o n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptiveCovLowerClose.acl_fk_q2_poincare_adaptive G hp hp1 hinj hcoh hadj o l hl disc₀ hdisc₀sup hoB ho n hn

/--
[acl_fixedFamily_route_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCovLowerClose.lean)
-/
@[path]
private lemma acl_fixedFamily_route_false_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {σf : κ → (Fin 3 ≃ Fin 3)}
  {k₀ : κ}
-- given
  (hk₀ : ((σf k₀).symm 0 : ℕ) = 0) :
-- imply
  ¬ PerScaleRevealmentClose.psr_FamilyFrontierConn σf (ReachDomination.indicatorConn PerScaleRevealmentClose.psr_witnessEndU PerScaleRevealmentClose.psr_witnessEndV ({0} : Set (Fin 4)) ({3} : Set (Fin 4))) PerScaleRevealmentClose.psr_witnessEndU PerScaleRevealmentClose.psr_witnessEndV (fun _ => ({0} : Set (Fin 4))) := by
-- proof
  apply StatMech.OSSS.AdaptiveCovLowerClose.acl_fixedFamily_route_false σf k₀ hk₀


-- created on 2026-10-23
