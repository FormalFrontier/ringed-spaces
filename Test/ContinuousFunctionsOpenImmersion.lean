/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces

/-!
# Ordinary-import tests for continuous-function open immersions
-/

open CategoryTheory TopologicalSpace Topology AlgebraicGeometry

universe u

namespace ContinuousFunctionsTest

variable (U X : Type u) [TopologicalSpace U] [TopologicalSpace X]
variable (K : Type u) [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T1Space K]

example (j : U → X) (hj : IsOpenEmbedding j) :
    LocallyRingedSpace.IsOpenImmersion
      (ContinuousFunctions.locallyRingedSpaceMap U K X j hj.continuous) := by
  haveI := ContinuousFunctions.locallyRingedSpaceMap_isOpenImmersion U X K j hj
  infer_instance

noncomputable example (A : Opens X) :
    (ContinuousFunctions.locallyRingedSpace X K).restrict A.isOpenEmbedding ≅
      ContinuousFunctions.locallyRingedSpace A K :=
  ContinuousFunctions.restrictLocallyRingedSpaceIso X K A

example (A : Opens X) :
    (ContinuousFunctions.restrictLocallyRingedSpaceIso X K A).hom ≫
        ContinuousFunctions.locallyRingedSpaceMap A K X Subtype.val
          A.isOpenEmbedding'.continuous =
      (ContinuousFunctions.locallyRingedSpace X K).ofRestrict A.isOpenEmbedding :=
  ContinuousFunctions.restrictLocallyRingedSpaceIso_hom_ofRestrict X K A

example (A : Opens X) :
    (ContinuousFunctions.restrictLocallyRingedSpaceIso X K A).inv ≫
        (ContinuousFunctions.locallyRingedSpace X K).ofRestrict A.isOpenEmbedding =
      ContinuousFunctions.locallyRingedSpaceMap A K X Subtype.val
        A.isOpenEmbedding'.continuous :=
  ContinuousFunctions.restrictLocallyRingedSpaceIso_inv_ofRestrict X K A

end ContinuousFunctionsTest
