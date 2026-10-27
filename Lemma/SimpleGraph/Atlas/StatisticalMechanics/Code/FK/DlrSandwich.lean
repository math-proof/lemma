import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.DlrSandwich
open SimpleGraph StatMech StatMech.FK


/--
[bcProb_free_le_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DlrSandwich.lean)
-/
@[path]
private lemma bcProb_free_le_bc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω := by
-- proof
  apply StatMech.FK.bcProb_free_le_bc G C hp hp1 hq hA

/--
[bcProb_bc_le_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DlrSandwich.lean)
-/
@[path]
private lemma bcProb_bc_le_wired_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hC : C ≤ StatMech.Lattice.boundaryCliqueGraph bdry)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω := by
-- proof
  apply StatMech.FK.bcProb_bc_le_wired G bdry C hC hp hp1 hq hA

/--
[bcProb_dlr_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DlrSandwich.lean)
-/
@[path]
private lemma bcProb_dlr_sandwich_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hC : C ≤ StatMech.Lattice.boundaryCliqueGraph bdry)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω ∧ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω := by
-- proof
  apply StatMech.FK.bcProb_dlr_sandwich G bdry C hC hp hp1 hq hA

/--
[bcProb_dlr_sandwich_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DlrSandwich.lean)
-/
@[path]
private lemma bcProb_dlr_sandwich_top_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω ∧ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊤ : SimpleGraph V) p q ω := by
-- proof
  apply StatMech.FK.bcProb_dlr_sandwich_top G bdry C hp hp1 hq hA

/--
[condFkProb_expect_eq_inducedFkProb_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DlrSandwich.lean)
-/
@[path]
private lemma condFkProb_expect_eq_inducedFkProb_expect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ : ConfigSpace (Sym2 V)}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ ω ∈ condFibre F ψ, f ω * condFkProb G p q F ψ ω) = ∑ ω ∈ condFibre F ψ, f ω * inducedFkProb G p q F ψ ω := by
-- proof
  apply StatMech.FK.condFkProb_expect_eq_inducedFkProb_expect G bdry hp hp1 hq F ψ f


-- created on 2026-10-23
