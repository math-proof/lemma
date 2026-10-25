/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalCandidateDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityCandidate.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogSingularity.Part2


namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexCanonicalEvenCommonHalfRoot
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) : Real :=
  sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + k)
    ⟨j.val, by omega⟩

def sixVertexCanonicalEvenBoundaryHalfRoot
    {c : Real} (hc : 2 < c) (s k : Nat) (i : Fin s) : Real :=
  sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + k)
    ⟨s + k + 1 + i.val, by omega⟩

def sixVertexCanonicalOddLeftHalfRoot
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) : Real :=
  sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)
    ⟨j.val, by omega⟩

def sixVertexCanonicalOddRightHalfRoot
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) : Real :=
  sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)
    ⟨j.val + 1, by omega⟩

def sixVertexCanonicalOddMidpointHalfRoot
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) : Real :=
  (sixVertexCanonicalOddLeftHalfRoot hc s k j +
    sixVertexCanonicalOddRightHalfRoot hc s k j) / 2

def sixVertexCanonicalOddBoundaryHalfRoot
    {c : Real} (hc : 2 < c) (s k : Nat) (i : Fin (s + 1)) : Real :=
  sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)
    ⟨s + k + 1 + i.val, by omega⟩

end
end StatMech.FrontierD
