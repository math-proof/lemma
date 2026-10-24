import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.SignOrthantTiling
open MeasureTheory Set Filter Topology Real SimpleGraph StatMech StatMech.FK


/--
[sot_repGraph_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean)
-/
@[path]
private lemma sot_repGraph_succ_eq
  {V : Type}
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : ℕ} :
-- imply
  sot_repGraph V G (k + 1) = G ⊕g (sot_repGraph V G k) := by
-- proof
  apply StatMech.FK.sot_repGraph_succ V G k

/--
[sot_repGraph_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean)
-/
@[path]
private lemma sot_repGraph_zero_eq
  {V : Type}
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  sot_repGraph V G 0 = (⊥ : SimpleGraph PEmpty) := by
-- proof
  apply StatMech.FK.sot_repGraph_zero V G

/--
[sot_fkZ_bot_pempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean)
-/
@[path]
private lemma sot_fkZ_bot_pempty_eq
  {p q : ℝ} :
-- imply
  fkZ (⊥ : SimpleGraph PEmpty) p q = 1 := by
-- proof
  apply StatMech.FK.sot_fkZ_bot_pempty

/--
[sot_repGraph_Z_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean)
-/
@[path]
private lemma sot_repGraph_Z_ge_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∀ k, (fkZ G p q) ^ k ≤ fkZ (sot_repGraph V G k) p q := by
-- proof
  apply StatMech.FK.sot_repGraph_Z_ge V G hp hp1 hq

/--
[sot_edge_card_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean)
-/
@[path]
private lemma sot_edge_card_lower_eq
  {d n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (n : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1) ≤ ((boxGraph d n).edgeFinset.card : ℝ) := by
-- proof
  apply StatMech.FK.sot_edge_card_lower d n hd

/--
[sot_summable_of_surfaceBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean)
-/
@[path]
private lemma sot_summable_of_surfaceBound_eq
  {d : ℕ}
  {C : ℝ}
  {I : ℕ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hC : 0 ≤ C)
  (hI0 : ∀ j, 0 ≤ I j)
  (hIB : ∀ j, I j ≤ C * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)) :
-- imply
  Summable (fun j => I j / bxt_E d (2 ^ (j + 1))) := by
-- proof
  apply StatMech.FK.sot_summable_of_surfaceBound d hd C hC I hI0 hIB

/--
[sot_negLogDoublingBound_of_crossSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean)
-/
@[path]
private lemma sot_negLogDoublingBound_of_crossSplit_eq
  {d : ℕ}
  {t : ℝ}
  {C : ℝ}
-- given
  (hd : 1 ≤ d)
  (hC : 0 ≤ C)
  (hsplit : ∀ j, sot_OrthantCrossSplit d t C j) :
-- imply
  bxt_NegLogDoublingBound d t := by
-- proof
  apply StatMech.FK.sot_negLogDoublingBound_of_crossSplit d hd t C hC hsplit

/--
[sot_boxGraph_zero_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean)
-/
@[path]
private lemma sot_boxGraph_zero_eq_bot_eq
  {n : ℕ} :
-- imply
  boxGraph 0 n = ⊥ := by
-- proof
  apply StatMech.FK.sot_boxGraph_zero_eq_bot n

/--
[sot_orthantCrossSplit_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean)
-/
@[path]
private lemma sot_orthantCrossSplit_satisfiable_eq
  {t : ℝ}
  {j : ℕ} :
-- imply
  sot_OrthantCrossSplit 0 t 0 j := by
-- proof
  apply StatMech.FK.sot_orthantCrossSplit_satisfiable t j

/--
[sot_fk_uniqueness_of_orthantSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean)
-/
@[path]
private lemma sot_fk_uniqueness_of_orthantSplit_eq
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {C : ℝ}
  {osc : ℝ → ℕ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hC : 0 ≤ C)
  (hsplit : ∀ t, ∀ j, sot_OrthantCrossSplit d t C j)
  (hbdd : ∀ t, ∃ M : ℝ, ∀ j, |bxt_u d t (2 ^ j) / bxt_E d (2 ^ j)| ≤ M)
  (hosc : ∀ t, Tendsto (osc t) atTop (𝓝 0))
  (hsand : ∀ t, ∀ n, 1 ≤ n → |ivp2_tiltFreeEnergy (boxGraph d n) 2 t - ivp2_tiltFreeEnergy (boxGraph d (2 ^ (Nat.log 2 n))) 2 t| ≤ osc t (Nat.log 2 n))
  (hfreeRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t)
  (hwiredRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.sot_fk_uniqueness_of_orthantSplit hd N eb hEbox C hC hsplit hbdd osc hosc hsand hfreeRot hwiredRot

/--
[sot_residue_remark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean)
-/
@[path]
private lemma sot_residue_remark_eq :
-- imply
  True := by
-- proof
  apply StatMech.FK.sot_residue_remark


-- created on 2026-10-23
