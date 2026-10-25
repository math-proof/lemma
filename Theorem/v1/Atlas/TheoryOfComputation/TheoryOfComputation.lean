/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/TheoryOfComputation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.BPP.Part3
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.CFGPDAEquiv
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.LadderPSPACE
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.NLStrictPSPACE
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.NLSubsetP
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.NLSubsetSpaceLog2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.RegexToNFA
import Inductive.v1.Atlas.TheoryOfComputation.code.CFGtoPDA.Part2
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
import Def.v1.Atlas.TheoryOfComputation.code.CFLInterRegular
import Def.v1.Atlas.TheoryOfComputation.code.Clique.Part6
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Def.v1.Atlas.TheoryOfComputation.code.ConfigReachability
import Def.v1.Atlas.TheoryOfComputation.code.ContextFree.Part4
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part13
import Theorem.v1.Atlas.TheoryOfComputation.code.FixedPointTheorem
import Theorem.v1.Atlas.TheoryOfComputation.code.GNFA
import Def.v1.Atlas.TheoryOfComputation.code.GNFAToRegex
import Def.v1.Atlas.TheoryOfComputation.code.GeographyGame.Part2
import Def.v1.Atlas.TheoryOfComputation.code.GraphNonIsoIP.Part2
import Def.v1.Atlas.TheoryOfComputation.code.HierarchyTheorems.Part4
import Def.v1.Atlas.TheoryOfComputation.code.InteractiveProofs.Part2
import Def.v1.Atlas.TheoryOfComputation.code.LadderNSPACE.Part3
import Def.v1.Atlas.TheoryOfComputation.code.LogSpace.Part4
import Def.v1.Atlas.TheoryOfComputation.code.NFA
import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part8
import Def.v1.Atlas.TheoryOfComputation.code.NTMSimulation
import Def.v1.Atlas.TheoryOfComputation.code.NondeterministicTM
import Def.v1.Atlas.TheoryOfComputation.code.PolyEquivProb
import Abbrev.v1.Atlas.TheoryOfComputation.code.PolyTimeReducibility
import Def.v1.Atlas.TheoryOfComputation.code.Probabilistic.Part5
import Def.v1.Atlas.TheoryOfComputation.code.RecursionTheorem
import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
import Def.v1.Atlas.TheoryOfComputation.code.RegularIsCFL
import Def.v1.Atlas.TheoryOfComputation.code.RegularLanguages
import Def.v1.Atlas.TheoryOfComputation.code.SelfReference.Part7
import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
import Def.v1.Atlas.TheoryOfComputation.code.SharpSATCoNPHard.Part2
import Def.v1.Atlas.TheoryOfComputation.code.SharpSATInIP.Part3
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Theorem.v1.Atlas.TheoryOfComputation.code.TMCodingInstance
import Def.v1.Atlas.TheoryOfComputation.code.TMComposition
import Structure.v1.Atlas.TheoryOfComputation.code.Tableau
import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4


