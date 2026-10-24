/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/TheoryOfComputation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TheoryOfComputation.code.BPP
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.CFGPDAEquiv
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.LadderPSPACE
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.NLStrictPSPACE
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.NLSubsetP
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.NLSubsetSpaceLog2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.RegexToNFA
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.CFGtoPDA
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.CFGtoPDA
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.CFLInterRegular
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Clique
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.ConfigReachability
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.ContextFree
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Decidability
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.GNFA
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.GNFAToRegex
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.GraphNonIsoIP
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.HierarchyTheorems
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.LogSpace
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.NFA
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.NPCompleteness
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.PolyEquivProb
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.PolyTimeReducibility
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Probabilistic
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.RecursionTheorem
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.RegularIsCFL
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.RegularLanguages
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SelfReference
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SharpSATCoNPHard
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SharpSATInIP
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TMCodingInstance
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TMComposition
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.CFLInterRegular
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Clique
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Complexity
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.ConfigReachability
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.ContextFree
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Decidability
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.FixedPointTheorem
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.GNFA
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.GNFAToRegex
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.GeographyGame
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.GraphNonIsoIP
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.HierarchyTheorems
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.InteractiveProofs
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.LadderNSPACE
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.LogSpace
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.NFA
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.NPCompleteness
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.NTMSimulation
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.NondeterministicTM
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.PolyEquivProb
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.PolyTimeReducibility
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Probabilistic
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.RecursionTheorem
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Reductions
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.RegularIsCFL
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.RegularLanguages
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.SelfReference
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.SharpSAT
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.SharpSATCoNPHard
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.SharpSATInIP
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.SpaceComplexity
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.TMCodingInstance
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.TMComposition
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Tableau
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.TuringMachines
