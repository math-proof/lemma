import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenBoxGeneral.Part3
open Set SimpleGraph Finset StatMech StatMech.FrontierA


/--
[bgfd_update_inBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_update_inBox_eq
  {d : ℕ}
  {L : ℕ}
  {c x : Site d}
  {j : Fin d}
  {v : ℤ}
-- given
  (hx : bgfdInBox L c x)
  (hv : (v - c j).natAbs ≤ L) :
-- imply
  bgfdInBox L c (Function.update x j v) := by
-- proof
  apply StatMech.FrontierA.bgfd_update_inBox hx j hv

/--
[bgfd_mix_inBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_mix_inBox_eq
  {d : ℕ}
  {L : ℕ}
  {c x y : Site d}
  {k : ℕ}
-- given
  (hx : bgfdInBox L c x)
  (hy : bgfdInBox L c y) :
-- imply
  bgfdInBox L c (mixSite x y k) := by
-- proof
  apply StatMech.FrontierA.bgfd_mix_inBox hx hy k

/--
[bgfd_ascend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_ascend_eq
  {d : ℕ}
  {L : ℕ}
  {c : Site d}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (hopen : ∀ x y : Site d, bgfdInBox L c x → bgfdInBox L c y → (hypercubicLattice d).Adj x y → omega s(x, y) = true)
  (hx : bgfdInBox L c x) :
-- imply
  ∀ (k : ℕ) (a : ℤ), (a - c j).natAbs ≤ L → (a + (k : ℤ) - c j).natAbs ≤ L → Connected d omega (Function.update x j a) (Function.update x j (a + (k : ℤ))) := by
-- proof
  apply StatMech.FrontierA.bgfd_ascend hopen hx j

/--
[bgfd_update_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_update_conn_eq
  {d : ℕ}
  {L : ℕ}
  {c : Site d}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {a : ℤ}
-- given
  (hopen : ∀ x y : Site d, bgfdInBox L c x → bgfdInBox L c y → (hypercubicLattice d).Adj x y → omega s(x, y) = true)
  (hx : bgfdInBox L c x)
  (ha : (a - c j).natAbs ≤ L) :
-- imply
  Connected d omega x (Function.update x j a) := by
-- proof
  apply StatMech.FrontierA.bgfd_update_conn hopen hx j ha

/--
[bgfd_mix_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_mix_conn_eq
  {d : ℕ}
  {L : ℕ}
  {c : Site d}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hopen : ∀ x y : Site d, bgfdInBox L c x → bgfdInBox L c y → (hypercubicLattice d).Adj x y → omega s(x, y) = true)
  (hx : bgfdInBox L c x)
  (hy : bgfdInBox L c y) :
-- imply
  ∀ k, k ≤ d → Connected d omega x (mixSite x y k) := by
-- proof
  apply StatMech.FrontierA.bgfd_mix_conn hopen hx hy

/--
[bgfd_box_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_box_connected_eq
  {d : ℕ}
  {L : ℕ}
  {c : Site d}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hopen : ∀ x y : Site d, bgfdInBox L c x → bgfdInBox L c y → (hypercubicLattice d).Adj x y → omega s(x, y) = true)
  (hx : bgfdInBox L c x)
  (hy : bgfdInBox L c y) :
-- imply
  Connected d omega x y := by
-- proof
  apply StatMech.FrontierA.bgfd_box_connected hopen hx hy

/--
[bgfd_idx_iff_inBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_idx_iff_inBox_eq
  {d : ℕ}
  {L : ℕ}
  {j x : Site d} :
-- imply
  bgn_idx L x = j ↔ bgfdInBox L (bgfdCentre L j) x := by
-- proof
  apply StatMech.FrontierA.bgfd_idx_iff_inBox

/--
[bgfd_idx_centre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_idx_centre_eq
  {d : ℕ}
  {L : ℕ}
  {j : Site d} :
-- imply
  bgn_idx L (bgfdCentre L j) = j := by
-- proof
  apply StatMech.FrontierA.bgfd_idx_centre L j

/--
[bgfd_centre_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_centre_injective_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Function.Injective (bgfdCentre (d := d) L) := by
-- proof
  apply StatMech.FrontierA.bgfd_centre_injective L

/--
[bgfd_lat_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_lat_shift_eq
  {d : ℕ}
  {c x y : Site d} :
-- imply
  (hypercubicLattice d).Adj (x + c) (y + c) ↔ (hypercubicLattice d).Adj x y := by
-- proof
  apply StatMech.FrontierA.bgfd_lat_shift c x y

/--
[bgfd_idx_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_idx_shift_eq
  {d : ℕ}
  {L : ℕ}
  {j x : Site d} :
-- imply
  bgn_idx L (x + bgfdCentre L j) = bgn_idx L x + j := by
-- proof
  apply StatMech.FrontierA.bgfd_idx_shift L j x

/--
[bgfd_centre_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_centre_zero_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  bgfdCentre (d := d) L 0 = 0 := by
-- proof
  apply StatMech.FrontierA.bgfd_centre_zero L

/--
[bgfd_indexAllOpen_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean)
-/
@[path]
private lemma bgfd_indexAllOpen_connected_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {j : Site d}
  {x y : Site d}
-- given
  (hopen : BgfdIndexAllOpen omega L j)
  (hx : bgn_idx L x = j)
  (hy : bgn_idx L y = j) :
-- imply
  Connected d omega x y := by
-- proof
  apply StatMech.FrontierA.bgfd_indexAllOpen_connected hopen hx hy


-- created on 2026-10-23
