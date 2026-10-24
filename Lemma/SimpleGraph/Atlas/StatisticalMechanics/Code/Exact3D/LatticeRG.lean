import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.LatticeRG
open StatMech StatMech.Exact3D StatMech.Exact3D.PolymerSupport StatMech.Exact3D.LatticeRGData


/--
[blockRepresentative_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockRepresentative_apply_eq
  {d : ℕ}
  {scale : BlockScale}
  {b : BlockIndex d}
  {i : Fin d} :
-- imply
  blockRepresentative scale b i = (scale.L : ℤ) * b i := by
-- proof
  apply StatMech.Exact3D.blockRepresentative_apply scale b i

/--
[blockRepresentative_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockRepresentative_zero_eq
  {d : ℕ}
  {scale : BlockScale} :
-- imply
  blockRepresentative scale (0 : BlockIndex d) = (0 : Site d) := by
-- proof
  apply StatMech.Exact3D.blockRepresentative_zero scale

/--
[blockIndexOf_blockRepresentative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockIndexOf_blockRepresentative_eq
  {d : ℕ}
  {scale : BlockScale}
  {b : BlockIndex d} :
-- imply
  blockIndexOf scale (blockRepresentative scale b) = b := by
-- proof
  apply StatMech.Exact3D.blockIndexOf_blockRepresentative scale b

/--
[blockIndexOf_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockIndexOf_zero_eq
  {d : ℕ}
  {scale : BlockScale} :
-- imply
  blockIndexOf scale (0 : Site d) = (0 : BlockIndex d) := by
-- proof
  apply StatMech.Exact3D.blockIndexOf_zero scale

/--
[blockRemainder_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockRemainder_apply_eq
  {d : ℕ}
  {scale : BlockScale}
  {x : Site d}
  {i : Fin d} :
-- imply
  blockRemainder scale x i = x i % (scale.L : ℤ) := by
-- proof
  apply StatMech.Exact3D.blockRemainder_apply scale x i

/--
[blockRepresentative_blockIndexOf_add_blockRemainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockRepresentative_blockIndexOf_add_blockRemainder_eq
  {d : ℕ}
  {scale : BlockScale}
  {x : Site d} :
-- imply
  blockRepresentative scale (blockIndexOf scale x) + blockRemainder scale x = x := by
-- proof
  apply StatMech.Exact3D.blockRepresentative_blockIndexOf_add_blockRemainder scale x

/--
[blockRemainder_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockRemainder_nonneg_eq
  {d : ℕ}
  {scale : BlockScale}
  {x : Site d}
  {i : Fin d} :
-- imply
  0 ≤ blockRemainder scale x i := by
-- proof
  apply StatMech.Exact3D.blockRemainder_nonneg scale x i

/--
[blockRemainder_lt_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockRemainder_lt_scale_eq
  {d : ℕ}
  {scale : BlockScale}
  {x : Site d}
  {i : Fin d} :
-- imply
  blockRemainder scale x i < (scale.L : ℤ) := by
-- proof
  apply StatMech.Exact3D.blockRemainder_lt_scale scale x i

/--
[blockRemainder_natAbs_lt_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockRemainder_natAbs_lt_scale_eq
  {d : ℕ}
  {scale : BlockScale}
  {x : Site d}
  {i : Fin d} :
-- imply
  (blockRemainder scale x i).natAbs < scale.L := by
-- proof
  apply StatMech.Exact3D.blockRemainder_natAbs_lt_scale scale x i

/--
[blockRemainder_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockRemainder_zero_eq
  {d : ℕ}
  {scale : BlockScale} :
-- imply
  blockRemainder scale (0 : Site d) = (0 : Site d) := by
-- proof
  apply StatMech.Exact3D.blockRemainder_zero scale

/--
[blockRemainder_blockRepresentative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockRemainder_blockRepresentative_eq
  {d : ℕ}
  {scale : BlockScale}
  {b : BlockIndex d} :
-- imply
  blockRemainder scale (blockRepresentative scale b) = (0 : Site d) := by
-- proof
  apply StatMech.Exact3D.blockRemainder_blockRepresentative scale b

/--
[blockRemainder_eq_zero_iff_exists_blockRepresentative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockRemainder_eq_zero_iff_exists_blockRepresentative_eq
  {d : ℕ}
  {scale : BlockScale}
  {x : Site d} :
-- imply
  blockRemainder scale x = 0 ↔ ∃ b : BlockIndex d, blockRepresentative scale b = x := by
-- proof
  apply StatMech.Exact3D.blockRemainder_eq_zero_iff_exists_blockRepresentative scale x

/--
[blockIndexOf_blockRepresentative_add_of_remainder_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockIndexOf_blockRepresentative_add_of_remainder_bounds_eq
  {d : ℕ}
  {scale : BlockScale}
  {b : BlockIndex d}
  {r : Site d}
-- given
  (hr_nonneg : ∀ i : Fin d, 0 ≤ r i)
  (hr_lt : ∀ i : Fin d, r i < (scale.L : ℤ)) :
-- imply
  blockIndexOf scale (blockRepresentative scale b + r) = b := by
-- proof
  apply StatMech.Exact3D.blockIndexOf_blockRepresentative_add_of_remainder_bounds scale b r hr_nonneg hr_lt

/--
[blockRemainder_blockRepresentative_add_of_remainder_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma blockRemainder_blockRepresentative_add_of_remainder_bounds_eq
  {d : ℕ}
  {scale : BlockScale}
  {b : BlockIndex d}
  {r : Site d}
-- given
  (hr_nonneg : ∀ i : Fin d, 0 ≤ r i)
  (hr_lt : ∀ i : Fin d, r i < (scale.L : ℤ)) :
-- imply
  blockRemainder scale (blockRepresentative scale b + r) = r := by
-- proof
  apply StatMech.Exact3D.blockRemainder_blockRepresentative_add_of_remainder_bounds scale b r hr_nonneg hr_lt

/--
[block_decomposition_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma block_decomposition_unique_eq
  {d : ℕ}
  {scale : BlockScale}
  {b c : BlockIndex d}
  {r s : Site d}
-- given
  (hr_nonneg : ∀ i : Fin d, 0 ≤ r i)
  (hr_lt : ∀ i : Fin d, r i < (scale.L : ℤ))
  (hs_nonneg : ∀ i : Fin d, 0 ≤ s i)
  (hs_lt : ∀ i : Fin d, s i < (scale.L : ℤ))
  (h : blockRepresentative scale b + r = blockRepresentative scale c + s) :
-- imply
  b = c ∧ r = s := by
-- proof
  apply StatMech.Exact3D.block_decomposition_unique scale hr_nonneg hr_lt hs_nonneg hs_lt h

/--
[deterministicKernel_allowed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma deterministicKernel_allowed_eq
  {d : ℕ}
  {scale : BlockScale}
  {coarse : ConfigSpace (Site d) → ConfigSpace (BlockIndex d)}
  {σ : ConfigSpace (Site d)} :
-- imply
  (deterministicKernel scale coarse).allowed σ (coarse σ) := by
-- proof
  apply StatMech.Exact3D.deterministicKernel_allowed scale coarse σ

/--
[deterministicKernel_allowed_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma deterministicKernel_allowed_iff_eq
  {d : ℕ}
  {scale : BlockScale}
  {coarse : ConfigSpace (Site d) → ConfigSpace (BlockIndex d)}
  {σ : ConfigSpace (Site d)}
  {τ : ConfigSpace (BlockIndex d)} :
-- imply
  (deterministicKernel scale coarse).allowed σ τ ↔ τ = coarse σ := by
-- proof
  apply StatMech.Exact3D.deterministicKernel_allowed_iff scale coarse σ τ

/--
[mem_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma mem_def_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {x : Site d} :
-- imply
  x ∈ P ↔ x ∈ P.carrier := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.mem_def P x

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma ext_eq
  {d : ℕ}
  {P Q : PolymerSupport d}
-- given
  (h : ∀ x : Site d, x ∈ P ↔ x ∈ Q) :
-- imply
  P = Q := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.ext h

/--
[not_mem_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma not_mem_empty_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  x ∉ empty d := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.not_mem_empty x

/--
[union_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma union_carrier_eq
  {d : ℕ}
  {P Q : PolymerSupport d} :
-- imply
  (P ∪ Q).carrier = P.carrier ∪ Q.carrier := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.union_carrier P Q

/--
[mem_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma mem_union_eq
  {d : ℕ}
  {P Q : PolymerSupport d}
  {x : Site d} :
-- imply
  x ∈ P ∪ Q ↔ x ∈ P ∨ x ∈ Q := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.mem_union P Q x

/--
[empty_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma empty_union_eq
  {d : ℕ}
  {P : PolymerSupport d} :
-- imply
  empty d ∪ P = P := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.empty_union P

/--
[union_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma union_empty_eq
  {d : ℕ}
  {P : PolymerSupport d} :
-- imply
  P ∪ empty d = P := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.union_empty P

/--
[mem_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma mem_translate_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {v x : Site d} :
-- imply
  x ∈ P.translate v ↔ ∃ y, y ∈ P ∧ y + v = x := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.mem_translate P v x

/--
[mem_translate_iff_sub_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma mem_translate_iff_sub_mem_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {v x : Site d} :
-- imply
  x ∈ P.translate v ↔ x - v ∈ P := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.mem_translate_iff_sub_mem P v x

/--
[empty_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma empty_translate_eq
  {d : ℕ}
  {v : Site d} :
-- imply
  (empty d).translate v = empty d := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.empty_translate v

/--
[translate_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma translate_zero_eq
  {d : ℕ}
  {P : PolymerSupport d} :
-- imply
  P.translate (0 : Site d) = P := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.translate_zero P

/--
[translate_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma translate_translate_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {v w : Site d} :
-- imply
  (P.translate v).translate w = P.translate (v + w) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.translate_translate P v w

/--
[translate_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma translate_card_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {v : Site d} :
-- imply
  (P.translate v).carrier.card = P.carrier.card := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.translate_card P v

/--
[permuteCoordinatesSite_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma permuteCoordinatesSite_refl_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  permuteCoordinatesSite (Equiv.refl (Fin d)) x = x := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.permuteCoordinatesSite_refl x

/--
[permuteCoordinatesSite_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma permuteCoordinatesSite_trans_eq
  {d : ℕ}
  {σ τ : Equiv.Perm (Fin d)}
  {x : Site d} :
-- imply
  permuteCoordinatesSite τ (permuteCoordinatesSite σ x) = permuteCoordinatesSite (σ.trans τ) x := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.permuteCoordinatesSite_trans σ τ x

/--
[permuteCoordinatesSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma permuteCoordinatesSite_injective_eq
  {d : ℕ}
  {σ : Equiv.Perm (Fin d)} :
-- imply
  Function.Injective (permuteCoordinatesSite σ) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.permuteCoordinatesSite_injective σ

/--
[mem_permuteCoordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma mem_permuteCoordinates_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {σ : Equiv.Perm (Fin d)}
  {x : Site d} :
-- imply
  x ∈ P.permuteCoordinates σ ↔ ∃ y, y ∈ P ∧ permuteCoordinatesSite σ y = x := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.mem_permuteCoordinates P σ x

/--
[permuteCoordinates_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma permuteCoordinates_refl_eq
  {d : ℕ}
  {P : PolymerSupport d} :
-- imply
  P.permuteCoordinates (Equiv.refl (Fin d)) = P := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.permuteCoordinates_refl P

/--
[permuteCoordinates_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma permuteCoordinates_trans_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {σ τ : Equiv.Perm (Fin d)} :
-- imply
  (P.permuteCoordinates σ).permuteCoordinates τ = P.permuteCoordinates (σ.trans τ) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.permuteCoordinates_trans P σ τ

/--
[permuteCoordinates_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma permuteCoordinates_card_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {σ : Equiv.Perm (Fin d)} :
-- imply
  (P.permuteCoordinates σ).carrier.card = P.carrier.card := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.permuteCoordinates_card P σ

/--
[coordinateRadiusBound_blockRemainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateRadiusBound_blockRemainder_eq
  {d : ℕ}
  {scale : BlockScale}
  {x : Site d} :
-- imply
  coordinateRadiusBound (scale.L - 1) (blockRemainder scale x) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateRadiusBound_blockRemainder scale x

/--
[coordinateRadiusBound_iff_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateRadiusBound_iff_mem_box_eq
  {d R : ℕ}
  {x : Site d} :
-- imply
  coordinateRadiusBound R x ↔ x ∈ box d R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateRadiusBound_iff_mem_box

/--
[coordinateRadiusBound_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateRadiusBound_mono_eq
  {d R S : ℕ}
  {x : Site d}
-- given
  (hRS : R ≤ S)
  (hx : coordinateRadiusBound R x) :
-- imply
  coordinateRadiusBound S x := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateRadiusBound_mono hRS hx

/--
[coordinateRadiusBound_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateRadiusBound_add_eq
  {d R S : ℕ}
  {x y : Site d}
-- given
  (hx : coordinateRadiusBound R x)
  (hy : coordinateRadiusBound S y) :
-- imply
  coordinateRadiusBound (R + S) (x + y) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateRadiusBound_add hx hy

/--
[coordinateRadiusBound_permuteCoordinatesSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateRadiusBound_permuteCoordinatesSite_eq
  {d R : ℕ}
  {x : Site d}
  {σ : Equiv.Perm (Fin d)}
-- given
  (hx : coordinateRadiusBound R x) :
-- imply
  coordinateRadiusBound R (permuteCoordinatesSite σ x) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateRadiusBound_permuteCoordinatesSite σ hx

/--
[containedInBox_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma containedInBox_iff_eq
  {d R : ℕ}
  {P : PolymerSupport d} :
-- imply
  P.containedInBox R ↔ ∀ x ∈ P, x ∈ box d R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.containedInBox_iff

/--
[containedInBox_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma containedInBox_empty_eq
  {d R : ℕ} :
-- imply
  (empty d).containedInBox R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.containedInBox_empty

/--
[containedInBox_mono_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma containedInBox_mono_radius_eq
  {d R S : ℕ}
  {P : PolymerSupport d}
-- given
  (hRS : R ≤ S)
  (hP : P.containedInBox R) :
-- imply
  P.containedInBox S := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.containedInBox_mono_radius hRS hP

/--
[containedInBox_mono_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma containedInBox_mono_support_eq
  {d R : ℕ}
  {P Q : PolymerSupport d}
-- given
  (hPQ : ∀ {x : Site d}, x ∈ P → x ∈ Q)
  (hQ : Q.containedInBox R) :
-- imply
  P.containedInBox R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.containedInBox_mono_support hPQ hQ

/--
[containedInBox_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma containedInBox_translate_eq
  {d R S : ℕ}
  {P : PolymerSupport d}
  {v : Site d}
-- given
  (hP : P.containedInBox R)
  (hv : coordinateRadiusBound S v) :
-- imply
  (P.translate v).containedInBox (R + S) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.containedInBox_translate hP hv

/--
[containedInBox_permuteCoordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma containedInBox_permuteCoordinates_eq
  {d R : ℕ}
  {P : PolymerSupport d}
  {σ : Equiv.Perm (Fin d)}
-- given
  (hP : P.containedInBox R) :
-- imply
  (P.permuteCoordinates σ).containedInBox R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.containedInBox_permuteCoordinates σ hP

/--
[reflectCoordinatesSite_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma reflectCoordinatesSite_false_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  reflectCoordinatesSite (fun _ : Fin d => false) x = x := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.reflectCoordinatesSite_false x

/--
[reflectCoordinatesSite_reflectCoordinatesSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma reflectCoordinatesSite_reflectCoordinatesSite_eq
  {d : ℕ}
  {ε δ : CoordinateReflection d}
  {x : Site d} :
-- imply
  reflectCoordinatesSite δ (reflectCoordinatesSite ε x) = reflectCoordinatesSite (fun i => Bool.xor (ε i) (δ i)) x := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.reflectCoordinatesSite_reflectCoordinatesSite ε δ x

/--
[reflectCoordinatesSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma reflectCoordinatesSite_injective_eq
  {d : ℕ}
  {ε : CoordinateReflection d} :
-- imply
  Function.Injective (reflectCoordinatesSite ε) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.reflectCoordinatesSite_injective ε

/--
[mem_reflectCoordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma mem_reflectCoordinates_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {ε : CoordinateReflection d}
  {x : Site d} :
-- imply
  x ∈ P.reflectCoordinates ε ↔ ∃ y, y ∈ P ∧ reflectCoordinatesSite ε y = x := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.mem_reflectCoordinates P ε x

/--
[reflectCoordinates_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma reflectCoordinates_false_eq
  {d : ℕ}
  {P : PolymerSupport d} :
-- imply
  P.reflectCoordinates (fun _ : Fin d => false) = P := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.reflectCoordinates_false P

/--
[reflectCoordinates_reflectCoordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma reflectCoordinates_reflectCoordinates_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {ε δ : CoordinateReflection d} :
-- imply
  (P.reflectCoordinates ε).reflectCoordinates δ = P.reflectCoordinates (fun i => Bool.xor (ε i) (δ i)) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.reflectCoordinates_reflectCoordinates P ε δ

/--
[reflectCoordinates_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma reflectCoordinates_card_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {ε : CoordinateReflection d} :
-- imply
  (P.reflectCoordinates ε).carrier.card = P.carrier.card := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.reflectCoordinates_card P ε

/--
[coordinateRadiusBound_reflectCoordinatesSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateRadiusBound_reflectCoordinatesSite_eq
  {d R : ℕ}
  {x : Site d}
  {ε : CoordinateReflection d}
-- given
  (hx : coordinateRadiusBound R x) :
-- imply
  coordinateRadiusBound R (reflectCoordinatesSite ε x) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateRadiusBound_reflectCoordinatesSite ε hx

/--
[containedInBox_reflectCoordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma containedInBox_reflectCoordinates_eq
  {d R : ℕ}
  {P : PolymerSupport d}
  {ε : CoordinateReflection d}
-- given
  (hP : P.containedInBox R) :
-- imply
  (P.reflectCoordinates ε).containedInBox R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.containedInBox_reflectCoordinates ε hP

/--
[cubicTransformSite_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma cubicTransformSite_identity_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  cubicTransformSite (0 : Site d) (Equiv.refl (Fin d)) (fun _ : Fin d => false) x = x := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.cubicTransformSite_identity x

/--
[cubicTransformSite_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma cubicTransformSite_comp_eq
  {d : ℕ}
  {v w : Site d}
  {σ τ : Equiv.Perm (Fin d)}
  {ε δ : CoordinateReflection d}
  {x : Site d} :
-- imply
  cubicTransformSite w τ δ (cubicTransformSite v σ ε x) = cubicTransformSite (reflectCoordinatesSite δ (permuteCoordinatesSite τ v) + w) (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) x := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.cubicTransformSite_comp v w σ τ ε δ x

/--
[cubicTransformSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma cubicTransformSite_injective_eq
  {d : ℕ}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : CoordinateReflection d} :
-- imply
  Function.Injective (cubicTransformSite v σ ε) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.cubicTransformSite_injective v σ ε

/--
[mem_cubicTransform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma mem_cubicTransform_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : CoordinateReflection d}
  {x : Site d} :
-- imply
  x ∈ P.cubicTransform v σ ε ↔ ∃ y, y ∈ P ∧ cubicTransformSite v σ ε y = x := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.mem_cubicTransform P v σ ε x

/--
[cubicTransform_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma cubicTransform_card_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : CoordinateReflection d} :
-- imply
  (P.cubicTransform v σ ε).carrier.card = P.carrier.card := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.cubicTransform_card P v σ ε

/--
[cubicTransform_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma cubicTransform_identity_eq
  {d : ℕ}
  {P : PolymerSupport d} :
-- imply
  P.cubicTransform (0 : Site d) (Equiv.refl (Fin d)) (fun _ : Fin d => false) = P := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.cubicTransform_identity P

/--
[cubicTransform_cubicTransform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma cubicTransform_cubicTransform_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {v w : Site d}
  {σ τ : Equiv.Perm (Fin d)}
  {ε δ : CoordinateReflection d} :
-- imply
  (P.cubicTransform v σ ε).cubicTransform w τ δ = P.cubicTransform (reflectCoordinatesSite δ (permuteCoordinatesSite τ v) + w) (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.cubicTransform_cubicTransform P v w σ τ ε δ

/--
[cubicTransform_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma cubicTransform_inverse_eq
  {d : ℕ}
  {P : PolymerSupport d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : CoordinateReflection d} :
-- imply
  (P.cubicTransform v σ ε).cubicTransform (cubicInverseTranslation v σ ε) σ.symm (fun i => ε (σ i)) = P := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.cubicTransform_inverse P v σ ε

/--
[containedInBox_cubicTransform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma containedInBox_cubicTransform_eq
  {d R S : ℕ}
  {P : PolymerSupport d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : CoordinateReflection d}
-- given
  (hP : P.containedInBox R)
  (hv : coordinateRadiusBound S v) :
-- imply
  (P.cubicTransform v σ ε).containedInBox (R + S) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.containedInBox_cubicTransform σ ε hP hv

/--
[containedInBox_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma containedInBox_union_eq
  {d R : ℕ}
  {P Q : PolymerSupport d} :
-- imply
  (P ∪ Q).containedInBox R ↔ P.containedInBox R ∧ Q.containedInBox R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.containedInBox_union P Q

/--
[containedInBox_union_intro](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma containedInBox_union_intro_eq
  {d R : ℕ}
  {P Q : PolymerSupport d}
-- given
  (hP : P.containedInBox R)
  (hQ : Q.containedInBox R) :
-- imply
  (P ∪ Q).containedInBox R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.containedInBox_union_intro hP hQ

/--
[coordinateDiameterBound_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateDiameterBound_empty_eq
  {d R : ℕ} :
-- imply
  (empty d).coordinateDiameterBound R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateDiameterBound_empty

/--
[coordinateDiameterBound_mono_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateDiameterBound_mono_radius_eq
  {d R S : ℕ}
  {P : PolymerSupport d}
-- given
  (hRS : R ≤ S)
  (hP : P.coordinateDiameterBound R) :
-- imply
  P.coordinateDiameterBound S := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateDiameterBound_mono_radius hRS hP

/--
[coordinateDiameterBound_mono_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateDiameterBound_mono_support_eq
  {d R : ℕ}
  {P Q : PolymerSupport d}
-- given
  (hPQ : ∀ {x : Site d}, x ∈ P → x ∈ Q)
  (hQ : Q.coordinateDiameterBound R) :
-- imply
  P.coordinateDiameterBound R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateDiameterBound_mono_support hPQ hQ

/--
[coordinateDiameterBound_of_containedInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateDiameterBound_of_containedInBox_eq
  {d R : ℕ}
  {P : PolymerSupport d}
-- given
  (hP : P.containedInBox R) :
-- imply
  P.coordinateDiameterBound (R + R) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateDiameterBound_of_containedInBox hP

/--
[coordinateDiameterBound_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateDiameterBound_translate_eq
  {d R : ℕ}
  {P : PolymerSupport d}
  {v : Site d}
-- given
  (hP : P.coordinateDiameterBound R) :
-- imply
  (P.translate v).coordinateDiameterBound R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateDiameterBound_translate hP

/--
[containedInBox_translate_neg_of_mem_of_coordinateDiameterBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma containedInBox_translate_neg_of_mem_of_coordinateDiameterBound_eq
  {d R : ℕ}
  {P : PolymerSupport d}
  {a : Site d}
-- given
  (ha : a ∈ P)
  (hP : P.coordinateDiameterBound R) :
-- imply
  (P.translate (-a)).containedInBox R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.containedInBox_translate_neg_of_mem_of_coordinateDiameterBound ha hP

/--
[exists_translate_containedInBox_of_nonempty_coordinateDiameterBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma exists_translate_containedInBox_of_nonempty_coordinateDiameterBound_eq
  {d R : ℕ}
  {P : PolymerSupport d}
-- given
  (hne : P.carrier.Nonempty)
  (hP : P.coordinateDiameterBound R) :
-- imply
  ∃ v : Site d, (P.translate v).containedInBox R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.exists_translate_containedInBox_of_nonempty_coordinateDiameterBound hne hP

/--
[coordinateDiameterBound_permuteCoordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateDiameterBound_permuteCoordinates_eq
  {d R : ℕ}
  {P : PolymerSupport d}
  {σ : Equiv.Perm (Fin d)}
-- given
  (hP : P.coordinateDiameterBound R) :
-- imply
  (P.permuteCoordinates σ).coordinateDiameterBound R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateDiameterBound_permuteCoordinates σ hP

/--
[coordinateDiameterBound_reflectCoordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateDiameterBound_reflectCoordinates_eq
  {d R : ℕ}
  {P : PolymerSupport d}
  {ε : CoordinateReflection d}
-- given
  (hP : P.coordinateDiameterBound R) :
-- imply
  (P.reflectCoordinates ε).coordinateDiameterBound R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateDiameterBound_reflectCoordinates ε hP

/--
[coordinateDiameterBound_cubicTransform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateDiameterBound_cubicTransform_eq
  {d R : ℕ}
  {P : PolymerSupport d}
  {v : Site d}
  {σ : Equiv.Perm (Fin d)}
  {ε : CoordinateReflection d}
-- given
  (hP : P.coordinateDiameterBound R) :
-- imply
  (P.cubicTransform v σ ε).coordinateDiameterBound R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateDiameterBound_cubicTransform σ ε hP

/--
[coordinateDiameterBound_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateDiameterBound_union_eq
  {d R : ℕ}
  {P Q : PolymerSupport d}
-- given
  (hP : P.coordinateDiameterBound R)
  (hQ : Q.coordinateDiameterBound R)
  (hCross : ∀ x ∈ P, ∀ y ∈ Q, ∀ i, (x i - y i).natAbs ≤ R) :
-- imply
  (P ∪ Q).coordinateDiameterBound R := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateDiameterBound_union hP hQ hCross

/--
[coordinateDiameterBound_union_of_containedInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma coordinateDiameterBound_union_of_containedInBox_eq
  {d R : ℕ}
  {P Q : PolymerSupport d}
-- given
  (hP : P.containedInBox R)
  (hQ : Q.containedInBox R) :
-- imply
  (P ∪ Q).coordinateDiameterBound (R + R) := by
-- proof
  apply StatMech.Exact3D.PolymerSupport.coordinateDiameterBound_union_of_containedInBox hP hQ

/--
[kernel_scale_eq_R_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma kernel_scale_eq_R_scale_eq
  {d : ℕ}
  {G : LatticeRGData d} :
-- imply
  G.kernel.scale = G.R.scale := by
-- proof
  apply StatMech.Exact3D.LatticeRGData.kernel_scale_eq_R_scale G

/--
[R_scale_eq_kernel_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma R_scale_eq_kernel_scale_eq
  {d : ℕ}
  {G : LatticeRGData d} :
-- imply
  G.R.scale = G.kernel.scale := by
-- proof
  apply StatMech.Exact3D.LatticeRGData.R_scale_eq_kernel_scale G

/--
[kernel_scale_toReal_eq_R_scale_toReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma kernel_scale_toReal_eq_R_scale_toReal_eq
  {d : ℕ}
  {G : LatticeRGData d} :
-- imply
  G.kernel.scale.toReal = G.R.scale.toReal := by
-- proof
  apply StatMech.Exact3D.LatticeRGData.kernel_scale_toReal_eq_R_scale_toReal G

/--
[R_scale_toReal_eq_kernel_scale_toReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean)
-/
@[path]
private lemma R_scale_toReal_eq_kernel_scale_toReal_eq
  {d : ℕ}
  {G : LatticeRGData d} :
-- imply
  G.R.scale.toReal = G.kernel.scale.toReal := by
-- proof
  apply StatMech.Exact3D.LatticeRGData.R_scale_toReal_eq_kernel_scale_toReal G


-- created on 2026-10-23
