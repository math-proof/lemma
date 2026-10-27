import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCovLowerGeom
open Finset Set StatMech StatMech.OSSS StatMech.OSSS.AdaptiveCovLowerGeom


/--
[hcov_crossTree_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCovLowerGeom.lean)
-/
@[path]
private lemma hcov_crossTree_mass_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {l : List E}
  {disc₀ : ℕ → Finset (Site d)}
  {n : ℕ}
  {D : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hl : ∀ e, e ∈ l)
  (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
  (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
  (hoB : ∀ k, o ∉ disc₀ k)
  (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
  (hn : 1 ≤ n)
  (hD : 0 < D)
  (hsum : ∀ e : E, (∑ k : ↥(Finset.Icc 1 n), boxRevealG μ edge endU endV (k : ℕ) e) ≤ (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) * D) :
-- imply
  Lindeberg.mean μ (crossIndG edge o n) * (1 - Lindeberg.mean μ (crossIndG edge o n)) / D ≤ ∑ e, Lindeberg.cov μ (crossIndG edge o n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptiveCovLowerGeom.hcov_crossTree_mass μ hpos hμ1 hFKG hinj hcoh hadj o l hl disc₀ hdisc₀sub hdisc₀sup hoB ho n hn D hD hsum

/--
[hcov_lattice_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCovLowerGeom.lean)
-/
@[path]
private lemma hcov_lattice_mass_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {l : List E}
  {disc₀ : ℕ → Finset (Site d)}
  {n : ℕ}
  {Λ : Finset (Site d)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
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
  (hLu : ∀ e : E, endU e ∈ Λ)
  (hLv : ∀ e : E, endV e ∈ Λ)
  (hUbox : ∀ e : E, endU e ∈ box d n)
  (hVbox : ∀ e : E, endV e ∈ box d n) :
-- imply
  Lindeberg.mean μ (crossIndG edge o n) * (1 - Lindeberg.mean μ (crossIndG edge o n)) / (4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j) then (1 : ℝ) else 0)) / (n : ℝ)) ≤ ∑ e, Lindeberg.cov μ (crossIndG edge o n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptiveCovLowerGeom.hcov_lattice_mass μ hpos hμ1 hFKG hinj hcoh hadj o l hl disc₀ hdisc₀sub hdisc₀sup hoB ho n hn Λ hne hLu hLv hUbox hVbox

/--
[fk_q2_hcov_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCovLowerGeom.lean)
-/
@[path]
private lemma fk_q2_hcov_lattice_eq
  [Fintype E]
  [DecidableEq E]
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
  (hLu : ∀ e : Sym2 W, endU e ∈ Λ)
  (hLv : ∀ e : Sym2 W, endV e ∈ Λ)
  (hUbox : ∀ e : Sym2 W, endU e ∈ box d n)
  (hVbox : ∀ e : Sym2 W, endV e ∈ box d n) :
-- imply
  Lindeberg.mean (fkMass G p 2) (crossInd edge o n) * (1 - Lindeberg.mean (fkMass G p 2) (crossInd edge o n)) / (4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, Lindeberg.mean (fkMass G p 2) (fun ω => if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j) then (1 : ℝ) else 0)) / (n : ℝ)) ≤ ∑ e, Lindeberg.cov (fkMass G p 2) (crossInd edge o n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptiveCovLowerGeom.fk_q2_hcov_lattice G hp hp1 hinj hcoh hadj o l hl disc₀ hdisc₀sub hdisc₀sup hoB ho n hn Λ hne hLu hLv hUbox hVbox


-- created on 2026-10-23
