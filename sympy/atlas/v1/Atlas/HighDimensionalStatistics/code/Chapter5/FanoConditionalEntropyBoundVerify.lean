/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/FanoConditionalEntropyBoundVerify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory

open MeasureTheory InformationTheory


#check @InfoTheory.fano_conditional_entropy_bound


#check @InfoTheory.data_processing_kl_partition
#check @InfoTheory.cond_entropy_fano_bound
#check @InfoTheory.fano_pointwise_entropy_bound
#check @InfoTheory.posterior_entropy_le_error_bound
#check @InfoTheory.fano_entropy_core_bound
#check @InfoTheory.fano_avg_posterior_bound
#check @InfoTheory.reduction_to_testing_fano
