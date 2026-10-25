import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
open Finset Matrix StatMech StatMech.FrontierB


/--
[site1Coord_site1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma site1Coord_site1_eq
  {z : ℤ} :
-- imply
  site1Coord (site1 z) = z := by
-- proof
  apply StatMech.FrontierB.site1Coord_site1 z

/--
[site1_site1Coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma site1_site1Coord_eq
  {x : Site 1} :
-- imply
  site1 (site1Coord x) = x := by
-- proof
  apply StatMech.FrontierB.site1_site1Coord x

/--
[site1_mem_box_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma site1_mem_box_iff_eq
  {z : ℤ}
  {n : ℕ} :
-- imply
  site1 z ∈ box 1 n ↔ -(n : ℤ) ≤ z ∧ z ≤ (n : ℤ) := by
-- proof
  apply StatMech.FrontierB.site1_mem_box_iff z n

/--
[site1_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma site1_adj_iff_eq
  {z w : ℤ} :
-- imply
  (hypercubicLattice 1).Adj (site1 z) (site1 w) ↔ (z - w).natAbs = 1 := by
-- proof
  apply StatMech.FrontierB.site1_adj_iff z w

/--
[mem_bondFinsetTouch_mk_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma mem_bondFinsetTouch_mk_iff_eq
  {n : ℕ}
  {x y : Site 1} :
-- imply
  s(x, y) ∈ bondFinsetTouch 1 n ↔ (hypercubicLattice 1).Adj x y ∧ (x ∈ box 1 n ∨ y ∈ box 1 n) := by
-- proof
  apply StatMech.FrontierB.mem_bondFinsetTouch_mk_iff n x y

/--
[chainBond_mem_bondFinsetTouch_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma chainBond_mem_bondFinsetTouch_iff_eq
  {z : ℤ}
  {n : ℕ} :
-- imply
  chainBond z ∈ bondFinsetTouch 1 n ↔ -(n : ℤ) - 1 ≤ z ∧ z ≤ (n : ℤ) := by
-- proof
  apply StatMech.FrontierB.chainBond_mem_bondFinsetTouch_iff z n

/--
[adjacent_site1_eq_chainBond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma adjacent_site1_eq_chainBond_eq
  {x y : Site 1}
-- given
  (hadj : (hypercubicLattice 1).Adj x y) :
-- imply
  ∃ z : ℤ, s(x, y) = chainBond z := by
-- proof
  apply StatMech.FrontierB.adjacent_site1_eq_chainBond x y hadj

/--
[chainBondFinset_eq_bondFinsetTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma chainBondFinset_eq_bondFinsetTouch_eq
  {n : ℕ} :
-- imply
  chainBondFinset n = bondFinsetTouch 1 n := by
-- proof
  apply StatMech.FrontierB.chainBondFinset_eq_bondFinsetTouch n

/--
[site1_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma site1_injective_eq :
-- imply
  Function.Injective site1 := by
-- proof
  apply StatMech.FrontierB.site1_injective

/--
[chainBond_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma chainBond_injective_eq :
-- imply
  Function.Injective chainBond := by
-- proof
  apply StatMech.FrontierB.chainBond_injective

/--
[chainSiteFinset_eq_boxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma chainSiteFinset_eq_boxFinset_eq
  {n : ℕ} :
-- imply
  chainSiteFinset n = boxFinset 1 n := by
-- proof
  apply StatMech.FrontierB.chainSiteFinset_eq_boxFinset n

/--
[sum_bondFinsetTouch_eq_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma sum_bondFinsetTouch_eq_chain_eq
  {n : ℕ}
  {sigma : ConfigSpace (Site 1)} :
-- imply
  (∑ e ∈ bondFinsetTouch 1 n, bond sigma e) = ∑ z ∈ Finset.Icc (-(n : ℤ) - 1) (n : ℤ), spin sigma (site1 z) * spin sigma (site1 (z + 1)) := by
-- proof
  apply StatMech.FrontierB.sum_bondFinsetTouch_eq_chain n sigma

/--
[sum_boxFinset_eq_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma sum_boxFinset_eq_chain_eq
  {n : ℕ}
  {sigma : ConfigSpace (Site 1)} :
-- imply
  (∑ x ∈ boxFinset 1 n, spin sigma x) = ∑ z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), spin sigma (site1 z) := by
-- proof
  apply StatMech.FrontierB.sum_boxFinset_eq_chain n sigma

/--
[sum_range_eq_sum_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma sum_range_eq_sum_Icc_eq
  [AddCommMonoid M]
  {L : ℤ}
  {m : ℕ}
  {f : ℤ → M} :
-- imply
  (∑ k ∈ Finset.range (m + 1), f (L + k)) = ∑ z ∈ Finset.Icc L (L + m), f z := by
-- proof
  apply StatMech.FrontierB.sum_range_eq_sum_Icc L m f

/--
[sum_adjacent_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma sum_adjacent_half_eq
  {f : ℕ → ℝ}
  {m : ℕ} :
-- imply
  (∑ k ∈ Finset.range (m + 1), (f k + f (k + 1)) / 2) = (f 0 + f (m + 1)) / 2 + ∑ k ∈ Finset.range m, f (k + 1) := by
-- proof
  apply StatMech.FrontierB.sum_adjacent_half f m

/--
[transferSpin_boolTransferState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma transferSpin_boolTransferState_eq
  {b : Bool} :
-- imply
  transferSpin (boolTransferState b) = if b then 1 else -1 := by
-- proof
  apply StatMech.FrontierB.transferSpin_boolTransferState b

/--
[transferSpin_of_config](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma transferSpin_of_config_eq
  {sigma : ConfigSpace (Site 1)}
  {z : ℤ} :
-- imply
  transferSpin (boolTransferState (sigma (site1 z))) = spin sigma (site1 z) := by
-- proof
  apply StatMech.FrontierB.transferSpin_of_config sigma z

/--
[isingTransferReal_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma isingTransferReal_apply_eq
  {beta H : ℝ}
  {u v : Fin 2} :
-- imply
  isingTransferReal beta H u v = Real.exp (beta * transferSpin u * transferSpin v + (H / 2) * (transferSpin u + transferSpin v)) := by
-- proof
  apply StatMech.FrontierB.isingTransferReal_apply beta H u v

/--
[transferSpin_fvPathState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma transferSpin_fvPathState_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
  {k : ℕ}
-- given
  (tau : {x // x ∈ box 1 n} → Bool) :
-- imply
  transferSpin (fvPathState eta n tau k) = spin (glue eta tau) (site1 (-(n : ℤ) - 1 + k)) := by
-- proof
  apply StatMech.FrontierB.transferSpin_fvPathState eta n tau k

/--
[sum_bondFinsetTouch_eq_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma sum_bondFinsetTouch_eq_path_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (tau : {x // x ∈ box 1 n} → Bool) :
-- imply
  (∑ e ∈ bondFinsetTouch 1 n, bond (glue eta tau) e) = ∑ k ∈ Finset.range (2 * n + 2), transferSpin (fvPathState eta n tau k) * transferSpin (fvPathState eta n tau (k + 1)) := by
-- proof
  apply StatMech.FrontierB.sum_bondFinsetTouch_eq_path eta n tau

/--
[sum_boxFinset_eq_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma sum_boxFinset_eq_path_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (tau : {x // x ∈ box 1 n} → Bool) :
-- imply
  (∑ x ∈ boxFinset 1 n, spin (glue eta tau) x) = ∑ k ∈ Finset.range (2 * n + 1), transferSpin (fvPathState eta n tau (k + 1)) := by
-- proof
  apply StatMech.FrontierB.sum_boxFinset_eq_path eta n tau

/--
[fvWeight_eq_endpointFactor_mul_transferProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma fvWeight_eq_endpointFactor_mul_transferProduct_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (tau : {x // x ∈ box 1 n} → Bool)
  (beta h : ℝ) :
-- imply
  fvWeight eta n (bondFinsetTouch 1 n) beta h tau = Real.exp (-(beta * h / 2) * (transferSpin (fvPathState eta n tau 0) + transferSpin (fvPathState eta n tau (2 * n + 2)))) * fvTransferProduct eta n tau beta h := by
-- proof
  apply StatMech.FrontierB.fvWeight_eq_endpointFactor_mul_transferProduct eta n tau beta h

/--
[interiorStateEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma interiorStateEquiv_apply_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
  {k : Fin (2 * n + 1)}
-- given
  (tau : {x // x ∈ box 1 n} → Bool) :
-- imply
  interiorStateEquiv n tau k = fvPathState eta n tau (k.val + 1) := by
-- proof
  apply StatMech.FrontierB.interiorStateEquiv_apply eta n tau k

/--
[fvPathState_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma fvPathState_zero_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (tau : {x // x ∈ box 1 n} → Bool) :
-- imply
  fvPathState eta n tau 0 = fvLeftBoundaryState eta n := by
-- proof
  apply StatMech.FrontierB.fvPathState_zero eta n tau

/--
[fvPathState_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma fvPathState_right_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (tau : {x // x ∈ box 1 n} → Bool) :
-- imply
  fvPathState eta n tau (2 * n + 2) = fvRightBoundaryState eta n := by
-- proof
  apply StatMech.FrontierB.fvPathState_right eta n tau

/--
[matrix_pow_apply_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma matrix_pow_apply_walk_eq
  [Fintype E]
  [DecidableEq E]
  [CommSemiring R]
  {A : Matrix E E R} :
-- imply
  ∀ (n : ℕ) (i j : E), (A ^ n) i j = ∑ p : Fin n → E, (if (Fin.cons i p : Fin (n + 1) → E) (Fin.last n) = j then (1 : R) else 0) * ∏ k : Fin n, A ((Fin.cons i p : Fin (n + 1) → E) k.castSucc) (p k) := by
-- proof
  apply StatMech.FrontierB.matrix_pow_apply_walk A

/--
[matrix_pow_apply_eq_sum_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma matrix_pow_apply_eq_sum_open_eq
  [Fintype E]
  [DecidableEq E]
  [CommSemiring R]
  {A : Matrix E E R}
  {a b : E}
  {m : ℕ} :
-- imply
  (A ^ (m + 1)) a b = ∑ q : Fin m → E, openMatrixProduct A a b q := by
-- proof
  apply StatMech.FrontierB.matrix_pow_apply_eq_sum_open A a b m

/--
[interior_snoc_eq_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma interior_snoc_eq_path_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (tau : {x // x ∈ box 1 n} → Bool) :
-- imply
  Fin.snoc (interiorStateEquiv n tau) (fvRightBoundaryState eta n) = fun k : Fin (2 * n + 2) => fvPathState eta n tau (k.val + 1) := by
-- proof
  apply StatMech.FrontierB.interior_snoc_eq_path eta n tau

/--
[boundary_cons_snoc_eq_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma boundary_cons_snoc_eq_path_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (tau : {x // x ∈ box 1 n} → Bool) :
-- imply
  Fin.cons (fvLeftBoundaryState eta n) (Fin.snoc (interiorStateEquiv n tau) (fvRightBoundaryState eta n)) = fun k : Fin (2 * n + 3) => fvPathState eta n tau k.val := by
-- proof
  apply StatMech.FrontierB.boundary_cons_snoc_eq_path eta n tau

/--
[fvTransferProduct_eq_openMatrixProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma fvTransferProduct_eq_openMatrixProduct_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (tau : {x // x ∈ box 1 n} → Bool)
  (beta h : ℝ) :
-- imply
  fvTransferProduct eta n tau beta h = openMatrixProduct (isingTransferReal beta (beta * h)) (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) (interiorStateEquiv n tau) := by
-- proof
  apply StatMech.FrontierB.fvTransferProduct_eq_openMatrixProduct eta n tau beta h

/--
[sum_fvTransferProduct_eq_matrix_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma sum_fvTransferProduct_eq_matrix_pow_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  (∑ tau : {x // x ∈ box 1 n} → Bool, fvTransferProduct eta n tau beta h) = (isingTransferReal beta (beta * h) ^ (2 * n + 2)) (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) := by
-- proof
  apply StatMech.FrontierB.sum_fvTransferProduct_eq_matrix_pow eta n beta h

/--
[fvWeight_eq_endpointFactor_mul_openProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma fvWeight_eq_endpointFactor_mul_openProduct_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (tau : {x // x ∈ box 1 n} → Bool)
  (beta h : ℝ) :
-- imply
  fvWeight eta n (bondFinsetTouch 1 n) beta h tau = fvEndpointFactor eta n beta h * fvTransferProduct eta n tau beta h := by
-- proof
  apply StatMech.FrontierB.fvWeight_eq_endpointFactor_mul_openProduct eta n tau beta h

/--
[fvZ_eq_endpointFactor_mul_matrix_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma fvZ_eq_endpointFactor_mul_matrix_pow_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  fvZ eta n (bondFinsetTouch 1 n) beta h = fvEndpointFactor eta n beta h * (isingTransferReal beta (beta * h) ^ (2 * n + 2)) (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) := by
-- proof
  apply StatMech.FrontierB.fvZ_eq_endpointFactor_mul_matrix_pow eta n beta h

/--
[centerPathEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma centerPathEquiv_apply_eq
  {E : Type*}
  {n : ℕ}
  {s : E}
  {l r : Fin n → E}
  {k : Fin (2 * n + 1)} :
-- imply
  centerPathEquiv E n (s,(l,r)) k = Fin.append l (Fin.cons s r) (Fin.cast (by omega) k) := by
-- proof
  apply StatMech.FrontierB.centerPathEquiv_apply E n s l r k

/--
[centerPathEquiv_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma centerPathEquiv_center_eq
  {E : Type*}
  {n : ℕ}
  {s : E}
  {l r : Fin n → E} :
-- imply
  centerPathEquiv E n (s,(l,r)) ⟨n, by omega⟩ = s := by
-- proof
  apply StatMech.FrontierB.centerPathEquiv_center E n s l r

/--
[centerPathEquiv_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma centerPathEquiv_left_eq
  {E : Type*}
  {n : ℕ}
  {s : E}
  {l r : Fin n → E}
  {i : Fin n} :
-- imply
  centerPathEquiv E n (s,(l,r)) ⟨i.val, by omega⟩ = l i := by
-- proof
  apply StatMech.FrontierB.centerPathEquiv_left E n s l r i

/--
[centerPathEquiv_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma centerPathEquiv_right_eq
  {E : Type*}
  {n : ℕ}
  {s : E}
  {l r : Fin n → E}
  {i : Fin n} :
-- imply
  centerPathEquiv E n (s,(l,r)) ⟨n + 1 + i.val, by omega⟩ = r i := by
-- proof
  apply StatMech.FrontierB.centerPathEquiv_right E n s l r i

/--
[fullPath_eq_pathVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma fullPath_eq_pathVertex_eq
  {m : ℕ}
  {a b : E}
  {q : Fin m → E}
  {k : Fin (m + 2)} :
-- imply
  (Fin.cons a (Fin.snoc q b) : Fin (m + 2) → E) k = pathVertex a b q k.val := by
-- proof
  apply StatMech.FrontierB.fullPath_eq_pathVertex a b q k

/--
[snoc_eq_pathVertex_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma snoc_eq_pathVertex_succ_eq
  {m : ℕ}
  {a b : E}
  {q : Fin m → E}
  {k : Fin (m + 1)} :
-- imply
  (Fin.snoc q b : Fin (m + 1) → E) k = pathVertex a b q (k.val + 1) := by
-- proof
  apply StatMech.FrontierB.snoc_eq_pathVertex_succ a b q k

/--
[openMatrixProduct_eq_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma openMatrixProduct_eq_nat_eq
  [Fintype E]
  [DecidableEq E]
  [CommSemiring R]
  {A : Matrix E E R}
  {a b : E}
  {m : ℕ}
  {q : Fin m → E} :
-- imply
  openMatrixProduct A a b q = openMatrixProductNat A a b q := by
-- proof
  apply StatMech.FrontierB.openMatrixProduct_eq_nat A a b q

/--
[pathVertex_center_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma pathVertex_center_left_eq
  {a s b : E}
  {n k : ℕ}
  {l r : Fin n → E}
-- given
  (hk : k ≤ n + 1) :
-- imply
  pathVertex a b (centerPathEquiv E n (s,(l,r))) k = pathVertex a s l k := by
-- proof
  apply StatMech.FrontierB.pathVertex_center_left a s b n k l r hk

/--
[pathVertex_center_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma pathVertex_center_right_eq
  {a s b : E}
  {n k : ℕ}
  {l r : Fin n → E}
-- given
  (hk : k ≤ n + 1) :
-- imply
  pathVertex a b (centerPathEquiv E n (s,(l,r))) (n + 1 + k) = pathVertex s b r k := by
-- proof
  apply StatMech.FrontierB.pathVertex_center_right a s b n k l r hk

/--
[openMatrixProduct_center_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma openMatrixProduct_center_factor_eq
  [Fintype E]
  [DecidableEq E]
  [CommSemiring R]
  {A : Matrix E E R}
  {a s b : E}
  {n : ℕ}
  {l r : Fin n → E} :
-- imply
  openMatrixProduct A a b (centerPathEquiv E n (s,(l,r))) = openMatrixProduct A a s l * openMatrixProduct A s b r := by
-- proof
  apply StatMech.FrontierB.openMatrixProduct_center_factor A a s b n l r

/--
[sum_openMatrixProduct_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma sum_openMatrixProduct_center_eq
  [Fintype E]
  [DecidableEq E]
  [CommSemiring R]
  {A : Matrix E E R}
  {a s b : E}
  {n : ℕ} :
-- imply
  (∑ q : Fin (2 * n + 1) → E, if q ⟨n, by omega⟩ = s then openMatrixProduct A a b q else 0) = (A ^ (n + 1)) a s * (A ^ (n + 1)) s b := by
-- proof
  apply StatMech.FrontierB.sum_openMatrixProduct_center A a s b n

/--
[interiorStateEquiv_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma interiorStateEquiv_center_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (tau : {x // x ∈ box 1 n} → Bool) :
-- imply
  interiorStateEquiv n tau ⟨n, by omega⟩ = fvPathState eta n tau (n + 1) := by
-- proof
  apply StatMech.FrontierB.interiorStateEquiv_center eta n tau

/--
[sum_fvTransferProduct_center_eq_matrix_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma sum_fvTransferProduct_center_eq_matrix_pow_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
  {s : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  (∑ tau : {x // x ∈ box 1 n} → Bool, if fvPathState eta n tau (n + 1) = s then fvTransferProduct eta n tau beta h else 0) = (isingTransferReal beta (beta * h) ^ (n + 1)) (fvLeftBoundaryState eta n) s * (isingTransferReal beta (beta * h) ^ (n + 1)) s (fvRightBoundaryState eta n) := by
-- proof
  apply StatMech.FrontierB.sum_fvTransferProduct_center_eq_matrix_pow eta n beta h s

/--
[sum_fvWeight_center_eq_matrix_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma sum_fvWeight_center_eq_matrix_pow_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
  {s : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  (∑ tau : {x // x ∈ box 1 n} → Bool, if fvPathState eta n tau (n + 1) = s then fvWeight eta n (bondFinsetTouch 1 n) beta h tau else 0) = fvEndpointFactor eta n beta h * ((isingTransferReal beta (beta * h) ^ (n + 1)) (fvLeftBoundaryState eta n) s * (isingTransferReal beta (beta * h) ^ (n + 1)) s (fvRightBoundaryState eta n)) := by
-- proof
  apply StatMech.FrontierB.sum_fvWeight_center_eq_matrix_pow eta n beta h s

/--
[fvCenterStateProb_eq_matrix_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma fvCenterStateProb_eq_matrix_ratio_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
  {s : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  fvCenterStateProb eta n beta h s = ((isingTransferReal beta (beta * h) ^ (n + 1)) (fvLeftBoundaryState eta n) s * (isingTransferReal beta (beta * h) ^ (n + 1)) s (fvRightBoundaryState eta n)) / (isingTransferReal beta (beta * h) ^ (2 * n + 2)) (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) := by
-- proof
  apply StatMech.FrontierB.fvCenterStateProb_eq_matrix_ratio eta n beta h s

/--
[fvCenterStateProb_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma fvCenterStateProb_tendsto_eq
  {eta : ℕ → ConfigSpace (Site 1)}
  {s : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (fun n => fvCenterStateProb (eta n) n beta h s) Filter.atTop (nhds (isingTransferProjectorPlus beta (beta * h) s s)) := by
-- proof
  apply StatMech.FrontierB.fvCenterStateProb_tendsto eta beta h s

/--
[measurableSet_centerStateEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma measurableSet_centerStateEvent_eq
  {s : Fin 2} :
-- imply
  MeasurableSet (centerStateEvent s) := by
-- proof
  apply StatMech.FrontierB.measurableSet_centerStateEvent s

/--
[origin_one_eq_site1_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma origin_one_eq_site1_zero_eq :
-- imply
  origin 1 = site1 0 := by
-- proof
  apply StatMech.FrontierB.origin_one_eq_site1_zero

/--
[fvPathState_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma fvPathState_center_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
-- given
  (tau : {x // x ∈ box 1 n} → Bool) :
-- imply
  fvPathState eta n tau (n + 1) = boolTransferState (glue eta tau (origin 1)) := by
-- proof
  apply StatMech.FrontierB.fvPathState_center eta n tau

/--
[fvMeasure_centerStateEvent_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma fvMeasure_centerStateEvent_real_eq
  {eta : ConfigSpace (Site 1)}
  {n : ℕ}
  {s : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  (fvMeasure eta n (bondFinsetTouch 1 n) beta h).real (centerStateEvent s) = fvCenterStateProb eta n beta h s := by
-- proof
  apply StatMech.FrontierB.fvMeasure_centerStateEvent_real eta n beta h s

/--
[fvMeasure_centerStateEvent_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma fvMeasure_centerStateEvent_tendsto_eq
  {eta : ℕ → ConfigSpace (Site 1)}
  {s : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (fun n => (fvMeasure (eta n) n (bondFinsetTouch 1 n) beta h).real (centerStateEvent s)) Filter.atTop (nhds (isingTransferProjectorPlus beta (beta * h) s s)) := by
-- proof
  apply StatMech.FrontierB.fvMeasure_centerStateEvent_tendsto eta beta h s

/--
[splitPathEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma splitPathEquiv_apply_eq
  {E : Type*}
  {m n : ℕ}
  {s : E}
  {l : Fin m → E}
  {r : Fin n → E}
  {k : Fin (m + n + 1)} :
-- imply
  splitPathEquiv E m n (s, (l, r)) k = Fin.append l (Fin.cons s r) (Fin.cast (by omega) k) := by
-- proof
  apply StatMech.FrontierB.splitPathEquiv_apply E m n s l r k

/--
[splitPathEquiv_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma splitPathEquiv_center_eq
  {E : Type*}
  {m n : ℕ}
  {s : E}
  {l : Fin m → E}
  {r : Fin n → E} :
-- imply
  splitPathEquiv E m n (s, (l, r)) ⟨m, by omega⟩ = s := by
-- proof
  apply StatMech.FrontierB.splitPathEquiv_center E m n s l r

/--
[splitPathEquiv_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma splitPathEquiv_left_eq
  {E : Type*}
  {m n : ℕ}
  {s : E}
  {l : Fin m → E}
  {r : Fin n → E}
  {i : Fin m} :
-- imply
  splitPathEquiv E m n (s, (l, r)) ⟨i.val, by omega⟩ = l i := by
-- proof
  apply StatMech.FrontierB.splitPathEquiv_left E m n s l r i

/--
[splitPathEquiv_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma splitPathEquiv_right_eq
  {E : Type*}
  {m n : ℕ}
  {s : E}
  {l : Fin m → E}
  {r : Fin n → E}
  {i : Fin n} :
-- imply
  splitPathEquiv E m n (s, (l, r)) ⟨m + 1 + i.val, by omega⟩ = r i := by
-- proof
  apply StatMech.FrontierB.splitPathEquiv_right E m n s l r i

/--
[pathVertex_split_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma pathVertex_split_left_eq
  {a s b : E}
  {m n k : ℕ}
  {l : Fin m → E}
  {r : Fin n → E}
-- given
  (hk : k ≤ m + 1) :
-- imply
  pathVertex a b (splitPathEquiv E m n (s, (l, r))) k = pathVertex a s l k := by
-- proof
  apply StatMech.FrontierB.pathVertex_split_left a s b m n k l r hk

/--
[pathVertex_split_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma pathVertex_split_right_eq
  {a s b : E}
  {m n k : ℕ}
  {l : Fin m → E}
  {r : Fin n → E}
-- given
  (hk : k ≤ n + 1) :
-- imply
  pathVertex a b (splitPathEquiv E m n (s, (l, r))) (m + 1 + k) = pathVertex s b r k := by
-- proof
  apply StatMech.FrontierB.pathVertex_split_right a s b m n k l r hk

/--
[openMatrixProduct_split_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma openMatrixProduct_split_factor_eq
  [Fintype E]
  [DecidableEq E]
  [CommSemiring R]
  {A : Matrix E E R}
  {a s b : E}
  {m n : ℕ}
  {l : Fin m → E}
  {r : Fin n → E} :
-- imply
  openMatrixProduct A a b (splitPathEquiv E m n (s, (l, r))) = openMatrixProduct A a s l * openMatrixProduct A s b r := by
-- proof
  apply StatMech.FrontierB.openMatrixProduct_split_factor A a s b m n l r

/--
[sum_openMatrixProduct_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean)
-/
@[path]
private lemma sum_openMatrixProduct_split_eq
  [Fintype E]
  [DecidableEq E]
  [CommSemiring R]
  {A : Matrix E E R}
  {a s b : E}
  {m n : ℕ} :
-- imply
  (∑ q : Fin (m + n + 1) → E, if q ⟨m, by omega⟩ = s then openMatrixProduct A a b q else 0) = (A ^ (m + 1)) a s * (A ^ (n + 1)) s b := by
-- proof
  apply StatMech.FrontierB.sum_openMatrixProduct_split A a s b m n


-- created on 2026-10-23
