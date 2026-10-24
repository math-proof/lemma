import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.ForestRootingClose
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[frc_connected_of_sameArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestRootingClose.lean)
-/
@[path]
private lemma frc_connected_of_sameArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x u v : Site d}
-- given
  (hxu : Connected d ω x u)
  (hneu : x ≠ u)
  (hxv : Connected d ω x v)
  (hnev : x ≠ v)
  (hsame : fsp_sameArm ω x u v) :
-- imply
  Connected d (removeSite x ω) u v := by
-- proof
  apply StatMech.Percolation.frc_connected_of_sameArm ω hxu hneu hxv hnev hsame

/--
[frc_claw_centralArm_connects_downstream](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestRootingClose.lean)
-/
@[path]
private lemma frc_claw_centralArm_connects_downstream_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
  {lx : Site d → Fin 3}
  {bx0 : Site d}
-- given
  (hx0_bx0_conn : Connected d ω x₀ bx0)
  (hx0_bx0_ne : x₀ ≠ bx0)
  (hx0_ycx_conn : Connected d ω x₀ (y (lx bx0)))
  (hx0_ycx_ne : x₀ ≠ y (lx bx0))
  (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v → (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
  (hydown : ∀ i, lx (y i) = i) :
-- imply
  Connected d (removeSite x₀ ω) bx0 (y (lx bx0)) := by
-- proof
  apply StatMech.Percolation.frc_claw_centralArm_connects_downstream ω hx0_bx0_conn hx0_bx0_ne hx0_ycx_conn hx0_ycx_ne hlxf hydown

/--
[frc_not_twoSidedPrivateFar_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestRootingClose.lean)
-/
@[path]
private lemma frc_not_twoSidedPrivateFar_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hclaw : stac_ClawConfig ω n) :
-- imply
  ¬ fps_TwoSidedPrivateFar ω n := by
-- proof
  apply StatMech.Percolation.frc_not_twoSidedPrivateFar_of_claw ω n hclaw

/--
[frc_claw_excludes_twoSidedPrivateFar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestRootingClose.lean)
-/
@[path]
private lemma frc_claw_excludes_twoSidedPrivateFar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hclaw : stac_ClawConfig ω n)
  (hres : fps_TwoSidedPrivateFar ω n) :
-- imply
  False := by
-- proof
  apply StatMech.Percolation.frc_claw_excludes_twoSidedPrivateFar ω n hclaw hres

/--
[frc_uniform_twoSidedPrivateFar_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestRootingClose.lean)
-/
@[path]
private lemma frc_uniform_twoSidedPrivateFar_false_eq
  {d : ℕ}
-- given
  (hex : ∃ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n ∧ stac_ClawConfig ω n) :
-- imply
  ¬ (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fps_TwoSidedPrivateFar ω n) := by
-- proof
  apply StatMech.Percolation.frc_uniform_twoSidedPrivateFar_false hex


-- created on 2026-10-23
