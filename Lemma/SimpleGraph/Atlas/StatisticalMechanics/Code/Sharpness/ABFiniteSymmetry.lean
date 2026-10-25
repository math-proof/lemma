import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteSymmetry.Part2
open Finset Set SimpleGraph StatMech StatMech.Sharpness


/--
[abfs_probV_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean)
-/
@[path]
private lemma abfs_probV_transfer_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  {e : E ≃ F}
  {A : Set (ConfigSpace E)}
-- given
  (p : E -> Real) :
-- imply
  probV p A = probV (fun y => p (e.symm y)) ((cfgEquiv e) ⁻¹' A) := by
-- proof
  apply StatMech.Sharpness.abfs_probV_transfer e p A

/--
[abfsOptionEquiv_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean)
-/
@[path]
private lemma abfsOptionEquiv_some_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {sigma : V ≃ V}
  {x : V} :
-- imply
  abfsOptionEquiv sigma (some x) = some (sigma x) := by
-- proof
  apply StatMech.Sharpness.abfsOptionEquiv_some G sigma x

/--
[abfsOptionEquiv_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean)
-/
@[path]
private lemma abfsOptionEquiv_none_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {sigma : V ≃ V} :
-- imply
  abfsOptionEquiv sigma none = none := by
-- proof
  apply StatMech.Sharpness.abfsOptionEquiv_none G sigma

/--
[abfsEdgeEquiv_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean)
-/
@[path]
private lemma abfsEdgeEquiv_mk_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {sigma : V ≃ V}
  {a b : Option V} :
-- imply
  abfsEdgeEquiv sigma s(a, b) = s(abfsOptionEquiv sigma a, abfsOptionEquiv sigma b) := by
-- proof
  apply StatMech.Sharpness.abfsEdgeEquiv_mk G sigma a b

/--
[abfs_openSub_adj_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean)
-/
@[path]
private lemma abfs_openSub_adj_relabel_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {sigma : V ≃ V}
  {omega : ConfigSpace (Sym2 (Option V))}
  {a b : Option V}
-- given
  (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y) :
-- imply
  (openSub (withGhost G) (cfgEquiv (abfsEdgeEquiv sigma) omega)).Adj a b <-> (openSub (withGhost G) omega).Adj (abfsOptionEquiv sigma a) (abfsOptionEquiv sigma b) := by
-- proof
  apply StatMech.Sharpness.abfs_openSub_adj_relabel G sigma hG omega a b

/--
[abfs_connWithin_univ_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean)
-/
@[path]
private lemma abfs_connWithin_univ_relabel_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {sigma : V ≃ V}
  {omega : ConfigSpace (Sym2 (Option V))}
  {a b : Option V}
-- given
  (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y) :
-- imply
  ConnWithin (withGhost G) (cfgEquiv (abfsEdgeEquiv sigma) omega) Set.univ ⟨a, Set.mem_univ _⟩ ⟨b, Set.mem_univ _⟩ <-> ConnWithin (withGhost G) omega Set.univ ⟨abfsOptionEquiv sigma a, Set.mem_univ _⟩ ⟨abfsOptionEquiv sigma b, Set.mem_univ _⟩ := by
-- proof
  apply StatMech.Sharpness.abfs_connWithin_univ_relabel G sigma hG omega a b

/--
[abfs_preimage_connEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean)
-/
@[path]
private lemma abfs_preimage_connEvent_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {sigma : V ≃ V}
  {o : V}
-- given
  (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y) :
-- imply
  (cfgEquiv (abfsEdgeEquiv sigma)) ⁻¹' connEvent (withGhost G) Set.univ (some o) {none} = connEvent (withGhost G) Set.univ (some (sigma o)) {none} := by
-- proof
  apply StatMech.Sharpness.abfs_preimage_connEvent G sigma hG o

/--
[abfs_params_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean)
-/
@[path]
private lemma abfs_params_invariant_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {sigma : V ≃ V}
  {e : Sym2 (Option V)}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y)
  (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y)) :
-- imply
  abfaParams G J beta h (abfsEdgeEquiv sigma e) = abfaParams G J beta h e := by
-- proof
  apply StatMech.Sharpness.abfs_params_invariant G J beta h sigma hG hJ e

/--
[abfs_mag_eq_of_automorphism](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean)
-/
@[path]
private lemma abfs_mag_eq_of_automorphism_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {sigma : V ≃ V}
-- given
  (J : Sym2 V -> Real)
  (beta h : Real)
  (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y)
  (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y)) :
-- imply
  probV (abfaParams G J beta h) (connEvent (withGhost G) Set.univ (some (sigma o)) {none}) = abfaMag G J o beta h := by
-- proof
  apply StatMech.Sharpness.abfs_mag_eq_of_automorphism G J o beta h sigma hG hJ

/--
[abfs_aizenmanBarsky_of_transitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean)
-/
@[path]
private lemma abfs_aizenmanBarsky_of_transitive_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (J : Sym2 V -> Real)
  (beta h J0 : Real)
  (hJnonneg : ∀ e ∈ G.edgeFinset, 0 <= J e)
  (hrow : forall x, abcrIncidentCoupling G J x = J0)
  (hbeta : 0 <= beta)
  (hh : 0 <= h)
  (move : V -> (V ≃ V))
  (hmove : forall x, move x o = x)
  (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
  (hJ : forall x u v, J s(move x u, move x v) = J s(u, v)) :
-- imply
  deriv (fun b => abfaMag G J o b h) beta <= J0 * abfaMag G J o beta h * deriv (fun t => abfaMag G J o beta t) h := by
-- proof
  apply StatMech.Sharpness.abfs_aizenmanBarsky_of_transitive G J o beta h J0 hJnonneg hrow hbeta hh move hmove hG hJ


-- created on 2026-10-23
