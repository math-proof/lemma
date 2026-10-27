import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.BoxFeketeData.Part2
open MeasureTheory Set Filter Topology Real StatMech StatMech.FK


/--
[bfd_tendsto_div_of_nearSubadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketeData.lean)
-/
@[path]
private lemma bfd_tendsto_div_of_nearSubadditive_eq
  {u c : ℕ → ℝ}
-- given
  (hsub : Subadditive (fun n => u n + c n))
  (hbdd : BddBelow (Set.range fun n => (u n + c n) / n))
  (hc : Tendsto (fun n => c n / n) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => u n / n) atTop (𝓝 hsub.lim) := by
-- proof
  apply StatMech.FK.bfd_tendsto_div_of_nearSubadditive u c hsub hbdd hc

/--
[bfd_tendsto_perEdge_of_nearSubadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketeData.lean)
-/
@[path]
private lemma bfd_tendsto_perEdge_of_nearSubadditive_eq
  {u c : ℕ → ℝ}
  {e : ℕ → ℝ}
  {κ : ℝ}
-- given
  (hsub : Subadditive (fun n => u n + c n))
  (hbdd : BddBelow (Set.range fun n => (u n + c n) / n))
  (hc : Tendsto (fun n => c n / n) atTop (𝓝 0))
  (hκ : κ ≠ 0)
  (he : Tendsto (fun n => e n / n) atTop (𝓝 κ)) :
-- imply
  Tendsto (fun n => u n / e n) atTop (𝓝 (hsub.lim / κ)) := by
-- proof
  apply StatMech.FK.bfd_tendsto_perEdge_of_nearSubadditive u c hsub hbdd hc e κ hκ he

/--
[bfd_tiltFreeEnergy_tendsto_of_nearSubadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketeData.lean)
-/
@[path]
private lemma bfd_tiltFreeEnergy_tendsto_of_nearSubadditive_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)]
  {q : ℝ}
  {t : ℝ}
  {c : ℕ → ℝ}
  {κ : ℝ}
-- given
  (hq : 0 < q)
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hsub : Subadditive (fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q) + c n))
  (hbdd : BddBelow (Set.range fun n => (- Real.log (fkZ (Gn n) (fsc_logistic t) q) + c n) / n))
  (hc : Tendsto (fun n => c n / n) atTop (𝓝 0))
  (hκ : κ ≠ 0)
  (he : Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 κ)) :
-- imply
  Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) q t) atTop (𝓝 (- (hsub.lim / κ) + Real.log (1 + Real.exp t))) := by
-- proof
  apply StatMech.FK.bfd_tiltFreeEnergy_tendsto_of_nearSubadditive q hq t hE c hsub hbdd hc κ hκ he

/--
[bfd_boxTiltFreeEnergy_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketeData.lean)
-/
@[path]
private lemma bfd_boxTiltFreeEnergy_tendsto_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)]
  {d : ℕ}
  {t : ℝ}
-- given
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hint : bfd_FKInterfaceData d t) :
-- imply
  ∃ L : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.bfd_boxTiltFreeEnergy_tendsto t hE hint

/--
[bfd_exists_convex_ivPressure_of_interface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketeData.lean)
-/
@[path]
private lemma bfd_exists_convex_ivPressure_of_interface_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)]
  {d : ℕ}
-- given
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hint : ∀ t, bfd_FKInterfaceData d t) :
-- imply
  ∃ g : ℝ → ℝ, (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t))) ∧ ConvexOn ℝ univ g := by
-- proof
  apply StatMech.FK.bfd_exists_convex_ivPressure_of_interface hE hint

/--
[bfd_fkInterfaceData_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketeData.lean)
-/
@[path]
private lemma bfd_fkInterfaceData_satisfiable_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)]
  {d : ℕ} :
-- imply
  ∃ (u c : ℕ → ℝ) (e : ℕ → ℝ) (κ : ℝ), Subadditive (fun n => u n + c n) ∧ BddBelow (Set.range fun n => (u n + c n) / n) ∧ Tendsto (fun n => c n / n) atTop (𝓝 0) ∧ κ ≠ 0 ∧ Tendsto (fun n => e n / n) atTop (𝓝 κ) := by
-- proof
  apply StatMech.FK.bfd_fkInterfaceData_satisfiable

/--
[bfd_fk_uniqueness_of_interface_and_uniformBulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketeData.lean)
-/
@[path]
private lemma bfd_fk_uniqueness_of_interface_and_uniformBulk_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)]
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hint : ∀ t, bfd_FKInterfaceData d t)
  (hfreeBulk : ubd_FreeUniformBulkDeviation (d := d) N)
  (hwiredBulk : ubd_WiredUniformBulkDeviation (d := d) N) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.bfd_fk_uniqueness_of_interface_and_uniformBulk hd N eb hEbox hint hfreeBulk hwiredBulk

/--
[bfd_residue_remark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketeData.lean)
-/
@[path]
private lemma bfd_residue_remark_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)]
  {d : ℕ} :
-- imply
  True := by
-- proof
  apply StatMech.FK.bfd_residue_remark


-- created on 2026-10-23
