import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.LocalizedCrossTree
open StatMech StatMech.OSSS StatMech.OSSS.LocalizedCrossTree


/--
[revealment_sum_bound_lattice_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LocalizedCrossTree.lean)
-/
@[path]
private lemma revealment_sum_bound_lattice_map_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype E]
  [DecidableEq E]
  {d : Nat}
  {Lambda : Finset (Site d)}
  {u : Site d}
-- given
  (mu : ConfigSpace E -> Real)
  (hmu0 : forall omega, 0 <= mu omega)
  (cfg : ConfigSpace E -> ConfigSpace I)
  (edge : I -> Sym2 (Site d))
  (hne : Lambda.Nonempty)
  (hu : u ∈ Lambda)
  (hubox : u ∈ box d n) :
-- imply
  (∑ k ∈ Finset.Icc 1 n, mean mu (fun omega => if ConnectedToSet d (liftCfg edge (cfg omega)) u (vertexBoundary d k) then (1 : Real) else 0)) <= 2 * Lambda.sup' hne (fun x => ∑ j ∈ Finset.range n, mean mu (fun omega => if ConnectedToSet d (liftCfg edge (cfg omega)) x (centeredBoundary x j) then (1 : Real) else 0)) := by
-- proof
  apply StatMech.OSSS.LocalizedCrossTree.revealment_sum_bound_lattice_map mu hmu0 cfg edge Lambda hne u hu hubox

/--
[hcov_reindexed_crossTree_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LocalizedCrossTree.lean)
-/
@[path]
private lemma hcov_reindexed_crossTree_mass_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype E]
  [DecidableEq E]
  {d : Nat}
  {edge : I -> Sym2 (Site d)}
  {endU endV : I -> Site d}
  {o : Site d}
  {l : List I}
  {n : Nat}
  {D : Real}
-- given
  (mu : ConfigSpace E -> Real)
  (hpos : forall omega, 0 < mu omega)
  (hmu1 : ∑ omega, mu omega = 1)
  (hFKG : FKGLatticeCondition mu)
  (iota : I -> E)
  (hiota : Function.Injective iota)
  (hinj : Function.Injective edge)
  (hcoh : forall i, edge i = s(endU i, endV i))
  (hadj : forall i, (hypercubicLattice d).Adj (endU i) (endV i))
  (hl : forall i, i ∈ l)
  (disc0 : Nat -> Finset (Site d))
  (hdisc0sub : ∀ k x, x ∈ disc0 k → x ∈ vertexBoundary d k)
  (hn : 1 <= n)
  (f : ConfigSpace E -> Real)
  (hf : Monotone f)
  (hidem : forall omega, f omega * f omega = f omega)
  (hcompute : forall (k : ↑(Finset.Icc 1 n)) (omega : ConfigSpace E), (crossTree endU endV o (vertexBoundary d n) l (disc0 (k : Nat))).evalR (restrictConfig iota omega) = f omega)
  (hD : 0 < D)
  (hsum : forall i : I, (∑ k : ↑(Finset.Icc 1 n), localizedBoxReveal mu iota edge endU endV (k : Nat) i) <= (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
-- imply
  Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) / D <= ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.LocalizedCrossTree.hcov_reindexed_crossTree_mass mu hpos hmu1 hFKG iota hiota hinj hcoh hadj o l hl disc0 hdisc0sub n hn f hf hidem hcompute D hD hsum


-- created on 2026-10-23
