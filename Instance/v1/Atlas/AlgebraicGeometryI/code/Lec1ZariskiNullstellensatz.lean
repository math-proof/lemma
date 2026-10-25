/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec1ZariskiNullstellensatz.Part2
open MvPolynomial AlgebraicGeometry CategoryTheory


namespace Lec1ZariskiNullstellensatz

noncomputable section

/-- The classical Zariski topology on affine space `k^σ`: closed sets are the zero loci of
ideals in `k[x_σ]`. -/
noncomputable instance zariskiTopology_classical
    (k : Type*) [Field k] (σ : Type*) [Fintype σ] :
    TopologicalSpace (σ → k) :=
  TopologicalSpace.ofClosed
    {V | ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus k I}
    ⟨⊤, MvPolynomial.zeroLocus_top.symm⟩
    (fun A hA => by

      have hchoice : ∀ V ∈ A, ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus k I :=
        fun V hV => hA hV
      let idealOf : (V : Set (σ → k)) → (V ∈ A) → Ideal (MvPolynomial σ k) :=
        fun V hV => Classical.choose (hchoice V hV)
      have hidealOf : ∀ V (hV : V ∈ A), V = MvPolynomial.zeroLocus k (idealOf V hV) :=
        fun V hV => Classical.choose_spec (hchoice V hV)
      refine ⟨⨆ (p : A), idealOf p.val p.prop, ?_⟩
      ext x
      simp only [Set.mem_sInter, MvPolynomial.mem_zeroLocus_iff]
      constructor
      · intro h f hf
        refine Submodule.iSup_induction (motive := fun g => (MvPolynomial.aeval x) g = 0) _ hf
          (fun ⟨V, hV⟩ g hg => ?_) (map_zero _) (fun a b ha hb => ?_)
        · have hxV : x ∈ V := h V hV
          rw [hidealOf V hV] at hxV
          exact hxV g hg
        · change (MvPolynomial.aeval x) a = 0 at ha
          change (MvPolynomial.aeval x) b = 0 at hb
          show (MvPolynomial.aeval x) (a + b) = 0
          rw [map_add, ha, hb, add_zero]
      · intro h V hV
        rw [hidealOf V hV]
        intro f hf
        exact h f (le_iSup (fun (p : A) => idealOf p.val p.prop) ⟨V, hV⟩ hf))
    (fun A ⟨I, hI⟩ B ⟨J, hJ⟩ => by

      refine ⟨I ⊓ J, ?_⟩
      subst hI; subst hJ
      ext x
      simp only [Set.mem_union, MvPolynomial.mem_zeroLocus_iff, Ideal.mem_inf]
      constructor
      · rintro (hI | hJ) f ⟨hfI, hfJ⟩
        · exact hI f hfI
        · exact hJ f hfJ
      · intro h
        by_contra hc
        push Not at hc
        obtain ⟨⟨f, hfI, hf⟩, ⟨g, hgJ, hg⟩⟩ := hc
        have hfg := h (f * g) ⟨I.mul_mem_right g hfI, J.mul_mem_left f hgJ⟩
        rw [map_mul] at hfg
        exact (mul_ne_zero hf hg) hfg)

end
end Lec1ZariskiNullstellensatz
