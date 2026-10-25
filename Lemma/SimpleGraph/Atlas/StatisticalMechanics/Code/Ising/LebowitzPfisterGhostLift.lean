import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterGhostLift.Part2
open Finset StatMech StatMech.Ising


/--
[lpGhostCoupling_some_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lpGhostCoupling_some_some_eq
  [Fintype V]
  [DecidableEq V]
  {x y : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  lpGhostCoupling J hf s(some x, some y) = J s(x, y) := by
-- proof
  apply StatMech.Ising.lpGhostCoupling_some_some J hf x y

/--
[lpGhostCoupling_some_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lpGhostCoupling_some_none_eq
  [Fintype V]
  [DecidableEq V]
  {x : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  lpGhostCoupling J hf s(some x, none) = hf x := by
-- proof
  apply StatMech.Ising.lpGhostCoupling_some_none J hf x

/--
[lpGhost_couplingSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lpGhost_couplingSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace (Option V)}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  (∑ e ∈ (withGhost G).edgeFinset, lpGhostCoupling J hf e * bond s e) = (∑ e ∈ G.edgeFinset, J e * bond (fun x => s (some x)) e) + spin s none * ∑ x : V, hf x * spin s (some x) := by
-- proof
  apply StatMech.Ising.lpGhost_couplingSum G J hf s

/--
[lpGhost_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lpGhost_weight_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace (Option V)}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  wJ (withGhost G).edgeFinset (lpGhostCoupling J hf) (fun _ => 0) s = wJ G.edgeFinset J (fun x => hf x * spin s none) (fun x => s (some x)) := by
-- proof
  apply StatMech.Ising.lpGhost_weight_eq G J hf s

/--
[lpGhost_ZJ_eq_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lpGhost_ZJ_eq_two_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  ZJ (withGhost G).edgeFinset (lpGhostCoupling J hf) (fun _ => 0) = 2 * ZJ G.edgeFinset J hf := by
-- proof
  apply StatMech.Ising.lpGhost_ZJ_eq_two_mul G J hf

/--
[lp_negField_even_numerator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lp_negField_even_numerator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (F : ConfigSpace V -> Real)
  (hF : forall s, F (FieldGhostDict.flipV s) = F s) :
-- imply
  (∑ s : ConfigSpace V, F s * wJ G.edgeFinset J (fun x => -hf x) s) = ∑ s : ConfigSpace V, F s * wJ G.edgeFinset J hf s := by
-- proof
  apply StatMech.Ising.lp_negField_even_numerator G J hf F hF

/--
[lpGhost_even_expJ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lpGhost_even_expJ_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (F : ConfigSpace V -> Real)
  (hF : forall s, F (FieldGhostDict.flipV s) = F s) :
-- imply
  expJ (withGhost G).edgeFinset (lpGhostCoupling J hf) (fun _ => 0) (fun s => F (fun x => s (some x))) = expJ G.edgeFinset J hf F := by
-- proof
  apply StatMech.Ising.lpGhost_even_expJ_eq G J hf F hF

/--
[lpGhost_twoPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lpGhost_twoPoint_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  grahamTwoPoint (withGhost G).edgeFinset (lpGhostCoupling J hf) (some x) (some y) = expJ G.edgeFinset J hf (fun s => spin s x * spin s y) := by
-- proof
  apply StatMech.Ising.lpGhost_twoPoint_eq G J hf x y

/--
[lpGhost_fourPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lpGhost_fourPoint_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  grahamFourPoint (withGhost G).edgeFinset (lpGhostCoupling J hf) (some i) (some j) (some k) (some l) = expJ G.edgeFinset J hf (fun s => (spin s i * spin s j) * (spin s k * spin s l)) := by
-- proof
  apply StatMech.Ising.lpGhost_fourPoint_eq G J hf i j k l

/--
[lpGhost_ursell4_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lpGhost_ursell4_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  grahamUrsell4 (withGhost G).edgeFinset (lpGhostCoupling J hf) (some i) (some j) (some k) (some l) = lpFieldUrsell4 G J hf i j k l := by
-- proof
  apply StatMech.Ising.lpGhost_ursell4_eq G J hf i j k l

/--
[lpGhostCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lpGhostCoupling_nonneg_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  forall e, 0 <= lpGhostCoupling J hf e := by
-- proof
  apply StatMech.Ising.lpGhostCoupling_nonneg J hf hJ hhf

/--
[lpField_lebowitz_four_point_le_leading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lpField_lebowitz_four_point_le_leading_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall x, 0 <= hf x)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  lpFieldUrsell4 G J hf i j k l <= -2 * (expJ G.edgeFinset J hf (fun s => spin s i * spin s l) * expJ G.edgeFinset J hf (fun s => spin s j * spin s l) * expJ G.edgeFinset J hf (fun s => spin s k * spin s l)) := by
-- proof
  apply StatMech.Ising.lpField_lebowitz_four_point_le_leading G J hf hJ hhf i j k l hij hik hil hjk hjl hkl

/--
[lpField_graham_four_point_strong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean)
-/
@[path]
private lemma lpField_graham_four_point_strong_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  2 * expJ G.edgeFinset J hf (fun s => spin s k * spin s l) * (expJ G.edgeFinset J hf (fun s => spin s i * spin s k) - expJ G.edgeFinset J hf (fun s => spin s i * spin s l) * expJ G.edgeFinset J hf (fun s => spin s k * spin s l)) * (expJ G.edgeFinset J hf (fun s => spin s j * spin s k) - expJ G.edgeFinset J hf (fun s => spin s j * spin s l) * expJ G.edgeFinset J hf (fun s => spin s k * spin s l)) <= (1 - expJ G.edgeFinset J hf (fun s => spin s k * spin s l) ^ 2) * (-(lpFieldUrsell4 G J hf i j k l + 2 * (expJ G.edgeFinset J hf (fun s => spin s i * spin s l) * expJ G.edgeFinset J hf (fun s => spin s j * spin s l) * expJ G.edgeFinset J hf (fun s => spin s k * spin s l)))) := by
-- proof
  apply StatMech.Ising.lpField_graham_four_point_strong G J hf hJ hhf i j k l


-- created on 2026-10-23
