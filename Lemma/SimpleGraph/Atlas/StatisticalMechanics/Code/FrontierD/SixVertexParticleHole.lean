import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexPositionsForwardInterlaced_of_forward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexPositionsForwardInterlaced_of_forward_eq
  {N n : ℕ}
  {x y : SixVertexSector N n}
-- given
  (h : SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y)) :
-- imply
  SixVertexPositionsForwardInterlaced x y := by
-- proof
  apply StatMech.FrontierD.sixVertexPositionsForwardInterlaced_of_forward x y h

/--
[sixVertexSectorPosition_le_iff_lt_prefixCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexSectorPosition_le_iff_lt_prefixCount_eq
  {N n : ℕ}
  {x : SixVertexSector N n}
  {i : Fin n}
  {k : Fin N} :
-- imply
  sixVertexSectorPosition x i ≤ k ↔ i.val < sixVertexSectorPrefixCount x k := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_le_iff_lt_prefixCount x i k

/--
[sixVertexSectorPrefixForward_of_positions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexSectorPrefixForward_of_positions_eq
  {N n : ℕ}
  {x y : SixVertexSector N n}
-- given
  (h : SixVertexPositionsForwardInterlaced x y) :
-- imply
  SixVertexSectorPrefixForward x y := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPrefixForward_of_positions x y h

/--
[sixVertexPositionsForwardInterlaced_of_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexPositionsForwardInterlaced_of_prefix_eq
  {N n : ℕ}
  {x y : SixVertexSector N n}
-- given
  (h : SixVertexSectorPrefixForward x y) :
-- imply
  SixVertexPositionsForwardInterlaced x y := by
-- proof
  apply StatMech.FrontierD.sixVertexPositionsForwardInterlaced_of_prefix x y h

/--
[sixVertexSectorParticleHoleEquiv_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexSectorParticleHoleEquiv_apply_val_eq
  {N n : ℕ}
  {x : SixVertexSector N n}
-- given
  (hn : n ≤ N) :
-- imply
  ((sixVertexSectorParticleHoleEquiv N n hn x : SixVertexSector N (N - n)) : Finset (Fin N)) = (x : Finset (Fin N))ᶜ := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorParticleHoleEquiv_apply_val hn x

/--
[sixVertexSectorRow_particleHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexSectorRow_particleHole_eq
  {N n : ℕ}
  {x : SixVertexSector N n}
  {i : Fin N}
-- given
  (hn : n ≤ N) :
-- imply
  sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x) i = !sixVertexSectorRow x i := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorRow_particleHole hn x i

/--
[sixVertexSectorPrefixCount_add_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexSectorPrefixCount_add_complement_eq
  {N n : ℕ}
  {x : SixVertexSector N n}
  {k : Fin N} :
-- imply
  sixVertexSectorPrefixCount x k + sixVertexSectorPrefixCount (sixVertexSectorComplement x) k = k.val + 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPrefixCount_add_complement x k

/--
[sixVertexSectorPrefixForward_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexSectorPrefixForward_complement_eq
  {N n : ℕ}
  {x y : SixVertexSector N n}
-- given
  (h : SixVertexSectorPrefixForward x y) :
-- imply
  SixVertexSectorPrefixForward (sixVertexSectorComplement y) (sixVertexSectorComplement x) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPrefixForward_complement x y h

/--
[sixVertexSectorPrefixForward_particleHole_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexSectorPrefixForward_particleHole_iff_eq
  {N n : ℕ}
  {x y : SixVertexSector N n}
-- given
  (hn : n ≤ N) :
-- imply
  SixVertexSectorPrefixForward (sixVertexSectorParticleHoleEquiv N n hn y) (sixVertexSectorParticleHoleEquiv N n hn x) ↔ SixVertexSectorPrefixForward x y := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPrefixForward_particleHole_iff hn x y

/--
[sixVertexInterlaced_particleHole_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexInterlaced_particleHole_imp_eq
  {N n : ℕ}
  {x y : SixVertexSector N n}
-- given
  (hn : n ≤ N)
  (h : SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y)) :
-- imply
  SixVertexInterlaced (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x)) (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn y)) := by
-- proof
  apply StatMech.FrontierD.sixVertexInterlaced_particleHole_imp hn x y h

/--
[sixVertexInterlaced_particleHole_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexInterlaced_particleHole_iff_eq
  {N n : ℕ}
  {x y : SixVertexSector N n}
-- given
  (hn : n ≤ N) :
-- imply
  SixVertexInterlaced (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x)) (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn y)) ↔ SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) := by
-- proof
  apply StatMech.FrontierD.sixVertexInterlaced_particleHole_iff hn x y

/--
[sixVertexRowDistance_particleHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexRowDistance_particleHole_eq
  {N n : ℕ}
  {x y : SixVertexSector N n}
-- given
  (hn : n ≤ N) :
-- imply
  sixVertexRowDistance (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x)) (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn y)) = sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) := by
-- proof
  apply StatMech.FrontierD.sixVertexRowDistance_particleHole hn x y

/--
[sixVertexSectorRow_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexSectorRow_injective_eq
  {N n : ℕ} :
-- imply
  Function.Injective (@sixVertexSectorRow N n) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorRow_injective

/--
[sixVertexSectorTransfer_particleHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_particleHole_eq
  {N n : ℕ}
  {c : ℝ}
  {x y : SixVertexSector N n}
-- given
  (hn : n ≤ N) :
-- imply
  sixVertexSectorTransfer N (N - n) c (sixVertexSectorParticleHoleEquiv N n hn x) (sixVertexSectorParticleHoleEquiv N n hn y) = sixVertexSectorTransfer N n c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_particleHole hn c x y

/--
[sixVertexSectorTransfer_reindex_particleHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_reindex_particleHole_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N) :
-- imply
  Matrix.reindex (sixVertexSectorParticleHoleEquiv N n hn) (sixVertexSectorParticleHoleEquiv N n hn) (sixVertexSectorTransfer N n c) = sixVertexSectorTransfer N (N - n) c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_reindex_particleHole hn c

/--
[sixVertexSectorTopEigenvalue_particleHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexSectorTopEigenvalue_particleHole_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N) :
-- imply
  sixVertexSectorTopEigenvalue N (N - n) (Nat.sub_le N n) c = sixVertexSectorTopEigenvalue N n hn c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTopEigenvalue_particleHole hn c

/--
[sixVertexLambda_particleHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean)
-/
@[path]
private lemma sixVertexLambda_particleHole_eq
  {N r : ℕ}
  {c : ℝ}
-- given
  (hN : Even N)
  (hr : r ≤ N / 2) :
-- imply
  sixVertexLambdaNeg N r hN hr c = sixVertexLambda N r hN hr c := by
-- proof
  apply StatMech.FrontierD.sixVertexLambda_particleHole N r hN hr c


-- created on 2026-10-23
