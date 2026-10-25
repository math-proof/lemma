import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc96bsignedinvolution.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc96b_threeGapCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc96bsignedinvolution.lean)
-/
@[path]
private lemma gc96b_threeGapCount_eq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc85b_threeGapCount ends m o x y g = (gc96b_signedPos ends m o x y g : ℤ) - (gc96b_signedNeg ends m o x y g : ℤ) := by
-- proof
  apply StatMech.Walls.gc96b_threeGapCount_eq ends m o x y g

/--
[gc96b_involution_iff_posLeNeg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc96bsignedinvolution.lean)
-/
@[path]
private lemma gc96b_involution_iff_posLeNeg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc96b_SignedInvolution ends m o x y g ↔ gc96b_signedPos ends m o x y g ≤ gc96b_signedNeg ends m o x y g := by
-- proof
  apply StatMech.Walls.gc96b_involution_iff_posLeNeg ends m o x y g

/--
[gc96b_fixed_points_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc96bsignedinvolution.lean)
-/
@[path]
private lemma gc96b_fixed_points_nonpos_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hinv : gc96b_SignedInvolution ends m o x y g) :
-- imply
  -(((gc96b_signedNeg ends m o x y g : ℤ) - (gc96b_signedPos ends m o x y g : ℤ))) ≤ 0 := by
-- proof
  apply StatMech.Walls.gc96b_fixed_points_nonpos ends m o x y g hinv

/--
[gc96b_threeGapCount_nonpos_of_involution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc96bsignedinvolution.lean)
-/
@[path]
private lemma gc96b_threeGapCount_nonpos_of_involution_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hinv : gc96b_SignedInvolution ends m o x y g) :
-- imply
  gc85b_threeGapCount ends m o x y g ≤ 0 := by
-- proof
  apply StatMech.Walls.gc96b_threeGapCount_nonpos_of_involution ends m o x y g hinv

/--
[gc96b_involution_iff_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc96bsignedinvolution.lean)
-/
@[path]
private lemma gc96b_involution_iff_bijection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc96b_SignedInvolution ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc96b_involution_iff_bijection ends m o x y g

/--
[gc96b_involution_closes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc96bsignedinvolution.lean)
-/
@[path]
private lemma gc96b_involution_closes_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hinv : gc96b_SignedInvolution ends m o x y g) :
-- imply
  gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc96b_involution_closes ends m o x y g hinv

/--
[gc96b_wred_pos_eq_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc96bsignedinvolution.lean)
-/
@[path]
private lemma gc96b_wred_pos_eq_neg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc96b_signedPos gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 = 7 ∧ gc96b_signedNeg gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 = 7 := by
-- proof
  apply StatMech.Walls.gc96b_wred_pos_eq_neg

/--
[gc96b_wred_equivariant_involution_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc96bsignedinvolution.lean)
-/
@[path]
private lemma gc96b_wred_equivariant_involution_exists_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc96b_SignedInvolution gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc96b_wred_equivariant_involution_exists

/--
[gc96b_star_involution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc96bsignedinvolution.lean)
-/
@[path]
private lemma gc96b_star_involution_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc96b_SignedInvolution gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3 ∧ gc96b_signedPos gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3 = 1 := by
-- proof
  apply StatMech.Walls.gc96b_star_involution

/--
[gc96b_signed_involution_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc96bsignedinvolution.lean)
-/
@[path]
private lemma gc96b_signed_involution_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  (gc96b_SignedInvolution ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g) ∧ (gc96b_SignedInvolution ends m o x y g → gc85b_threeGapCount ends m o x y g ≤ 0) ∧ gc96b_SignedInvolution gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc96b_signed_involution_status ends m o x y g

/--
[gc96b_machine_findings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc96bsignedinvolution.lean)
-/
@[path]
private lemma gc96b_machine_findings_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gc96b_machine_findings


-- created on 2026-10-23
