import Mathlib
import Def.ModularCurve_X0ModL
import Lemma.ModularCurve.QAdicPlaceMod
import Lemma.ModularCurve.ModuliPointMap
import Lemma.WeierstrassCurve.ReduceHom
import Lemma.WeierstrassCurve.CyclicQuotientJ
import Lemma.AlgebraicCurve.Correspondence
import Instance.ModularCurve_ModuliPlace

set_option autoImplicit false

noncomputable section

open IsLocalRing AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

namespace ModularCurve

universe u

section Generators

variable (K : Type*) [Field K] (N : ℕ)

theorem jqNModC_mem_full {d : ℕ} [NeZero d] (hd : d ∣ N) :
    jqNModC K d ∈ modularFunctionFieldFullC K N :=
  jqModCd_mem_full K N hd

def jqNFull (d : ℕ) [NeZero d] (hd : d ∣ N) : modularFunctionFieldFullC K N :=
  ⟨jqNModC K d, jqNModC_mem_full K N hd⟩


end Generators

namespace ComapPlace

variable {K F Ω : Type*} [Field K] [Field F] [Field Ω] [Algebra K Ω] (φ : F →+* Ω) (W : Place K Ω)


variable {φ W}


variable (hex : ∃ f : F, f ≠ 0 ∧ 0 < W.ord (φ f))
include hex


variable [Algebra K F]

omit hex in


end ComapPlace

section TestDatum

variable (K : Type u) [Field K] [DecidableEq K] (N : ℕ)

structure ModuliTestDatum (x : ModuliPoint N K) (Ω : Type u) [Field Ω] [DecidableEq Ω]
    [Algebra K Ω] where

  W : Place K Ω

  curve : WeierstrassCurve W.toValuationSubring

  map_Δ_ne_zero : (curve.map (residue W.toValuationSubring)).Δ ≠ 0

  gen : (curve.map W.toValuationSubring.subtype).toAffine.Point

  addOrderOf_gen : addOrderOf gen = N

  res : ResidueField W.toValuationSubring →+* K

  res_algebraMap : ∀ c : K, res (algebraMap K (ResidueField W.toValuationSubring) c) = c

  reduction :
    letI := Classical.decEq (ResidueField W.toValuationSubring)
    ∃ hord : addOrderOf (reduceHom map_Δ_ne_zero gen) = N,
      ModuliPoint.map res
        (Quot.mk _ (⟨curve.map (residue W.toValuationSubring),
          ⟨isUnit_iff_ne_zero.mpr map_Δ_ne_zero⟩, reduceHom map_Δ_ne_zero gen, hord⟩ :
            Gamma0Pair N (ResidueField W.toValuationSubring))) = x

  emb : modularFunctionFieldFullC K N →ₐ[K] Ω

  emb_jqNFull : ∀ (Ω' : Type u) [Field Ω'] [DecidableEq Ω'] [IsAlgClosed Ω'] [Algebra Ω Ω']
      (d : ℕ) [NeZero d] (hd : d ∣ N),
      algebraMap Ω Ω' (emb (jqNFull K N d hd)) =
        ((curve.map W.toValuationSubring.subtype).map (algebraMap Ω Ω')).cyclicQuotientJ
          (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint (algebraMap Ω Ω') ((N / d) • gen))) d


end TestDatum

namespace ModuliTestDatum

variable {K : Type u} [Field K] [DecidableEq K] {N : ℕ} {x : ModuliPoint N K}
  {Ω : Type u} [Field Ω] [DecidableEq Ω] [Algebra K Ω] (D : ModuliTestDatum K N x Ω)


variable {D} in


section RestrictLevel

variable [NeZero N] {M : ℕ} [NeZero M]

omit [NeZero M] in


variable (hMN : M ∣ N) (x' : ModuliPoint M K)
  (hx' : letI := Classical.decEq (ResidueField D.W.toValuationSubring)
    ModuliPoint.map D.res
      (Quot.mk _ (⟨D.curve.map (residue D.W.toValuationSubring),
        ⟨isUnit_iff_ne_zero.mpr D.map_Δ_ne_zero⟩, reduceHom D.map_Δ_ne_zero ((N / M) • D.gen),
          D.addOrderOf_reduceHom_levelGen hMN⟩ :
            Gamma0Pair M (ResidueField D.W.toValuationSubring))) = x')


end RestrictLevel

end ModuliTestDatum

section API

variable (K : Type u) [Field K] [DecidableEq K] (N : ℕ)

variable {K N} in


variable {K N} in
omit [DecidableEq K] in


variable {K N} in


end API

end ModularCurve

end
