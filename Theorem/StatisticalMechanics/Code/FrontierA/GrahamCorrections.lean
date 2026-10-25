/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Def.StatisticalMechanics.Code.FrontierA.GrahamCorrections


namespace StatMech.FrontierA

open Finset

open scoped symmDiff

open StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


omit [Fintype V] in

@[simp] theorem grahamPairSupport_chain (i m k : V) :
    grahamPairSupport i m ∆ grahamPairSupport m k = grahamPairSupport i k := by
  classical
  ext x
  simp only [grahamPairSupport, Finset.mem_symmDiff, Finset.mem_singleton]
  tauto

omit [Fintype V] in

theorem spinProd_grahamPairSupport (s : ConfigSpace V) (x y : V) :
    spinProd (grahamPairSupport x y) s = spin s x * spin s y := by
  simpa [grahamPairSupport, spinProd] using
    (spinProd_mul_self ({x} : Finset V) ({y} : Finset V) s).symm

omit [Fintype V] in

theorem spinProd_grahamFourSupport (s : ConfigSpace V) (i j k l : V) :
    spinProd (grahamFourSupport i j k l) s =
      (spin s i * spin s j) * (spin s k * spin s l) := by
  rw [grahamFourSupport, ← spinProd_mul_self, spinProd_grahamPairSupport,
    spinProd_grahamPairSupport]


theorem grahamTwoPoint_eq_expJ (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (x y : V) :
    grahamTwoPoint E J x y =
      expJ E J (fun _ => 0) (fun s => spin s x * spin s y) := by
  unfold grahamTwoPoint
  congr 1
  funext s
  exact spinProd_grahamPairSupport s x y


theorem grahamFourPoint_eq_expJ (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l : V) :
    grahamFourPoint E J i j k l =
      expJ E J (fun _ => 0)
        (fun s => (spin s i * spin s j) * (spin s k * spin s l)) := by
  unfold grahamFourPoint
  congr 1
  funext s
  exact spinProd_grahamFourSupport s i j k l


theorem grahamUrsell4_eq_expJ (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l : V) :
    grahamUrsell4 E J i j k l =
      expJ E J (fun _ => 0)
          (fun s => (spin s i * spin s j) * (spin s k * spin s l))
        - expJ E J (fun _ => 0) (fun s => spin s i * spin s j) *
            expJ E J (fun _ => 0) (fun s => spin s k * spin s l)
        - expJ E J (fun _ => 0) (fun s => spin s i * spin s k) *
            expJ E J (fun _ => 0) (fun s => spin s j * spin s l)
        - expJ E J (fun _ => 0) (fun s => spin s i * spin s l) *
            expJ E J (fun _ => 0) (fun s => spin s j * spin s k) := by
  rw [grahamUrsell4, grahamFourPoint_eq_expJ,
    grahamTwoPoint_eq_expJ, grahamTwoPoint_eq_expJ,
    grahamTwoPoint_eq_expJ, grahamTwoPoint_eq_expJ,
    grahamTwoPoint_eq_expJ, grahamTwoPoint_eq_expJ]


@[simp] theorem grahamTwoPoint_self (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (x : V) : grahamTwoPoint E J x x = 1 := by
  classical
  unfold grahamTwoPoint
  rw [show grahamPairSupport x x = ∅ by simp [grahamPairSupport]]
  unfold expJ
  rw [show (∑ s : ConfigSpace V, spinProd ∅ s * wJ E J (fun _ => 0) s) =
      ZJ E J (fun _ => 0) by simp [spinProd, ZJ]]
  exact div_self (ZJ_pos E J (fun _ => 0)).ne'


theorem grahamTwoPoint_comm (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (x y : V) : grahamTwoPoint E J x y = grahamTwoPoint E J y x := by
  unfold grahamTwoPoint grahamPairSupport
  rw [symmDiff_comm]


end StatMech.FrontierA
