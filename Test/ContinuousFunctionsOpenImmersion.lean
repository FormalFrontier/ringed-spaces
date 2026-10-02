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

section GeneralRing

variable (U X R : Type u) [TopologicalSpace U] [TopologicalSpace X]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

example (j : U → X) (hj : IsOpenEmbedding j) (V : Opens U) :
    IsIso ((ContinuousFunctions.ringedSpaceMap U R X j hj.continuous).hom.c.app
      (Opposite.op ((show IsOpenEmbedding
        (ContinuousFunctions.ringedSpaceMap U R X j hj.continuous).hom.base from hj).functor.obj V))) :=
  ContinuousFunctions.ringedSpaceMap_c_iso U X R j hj V

example (j : U → X) (hj : IsOpenEmbedding j) :
    SheafedSpace.IsOpenImmersion
      (ContinuousFunctions.ringedSpaceMap U R X j hj.continuous) := by
  letI := ContinuousFunctions.ringedSpaceMap_isOpenImmersion U X R j hj
  infer_instance

noncomputable example (A : Opens X) :
    ContinuousFunctions.ringedSpace A R ≅
      (ContinuousFunctions.ringedSpace X R).restrict A.isOpenEmbedding := by
  letI := ContinuousFunctions.ringedSpaceMap_isOpenImmersion
    A X R Subtype.val A.isOpenEmbedding'
  exact SheafedSpace.IsOpenImmersion.isoRestrict
    (ContinuousFunctions.ringedSpaceMap A R X Subtype.val A.isOpenEmbedding'.continuous)

example (A : Opens X) :
    (letI := ContinuousFunctions.ringedSpaceMap_isOpenImmersion
        A X R Subtype.val A.isOpenEmbedding';
      (SheafedSpace.IsOpenImmersion.isoRestrict
        (ContinuousFunctions.ringedSpaceMap A R X Subtype.val
          A.isOpenEmbedding'.continuous)).hom ≫
          (ContinuousFunctions.ringedSpace X R).ofRestrict A.isOpenEmbedding =
        ContinuousFunctions.ringedSpaceMap A R X Subtype.val
          A.isOpenEmbedding'.continuous) := by
  letI := ContinuousFunctions.ringedSpaceMap_isOpenImmersion
    A X R Subtype.val A.isOpenEmbedding'
  exact SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict
    (ContinuousFunctions.ringedSpaceMap A R X Subtype.val A.isOpenEmbedding'.continuous)

example (A : Opens X) :
    (letI := ContinuousFunctions.ringedSpaceMap_isOpenImmersion
        A X R Subtype.val A.isOpenEmbedding';
      (SheafedSpace.IsOpenImmersion.isoRestrict
        (ContinuousFunctions.ringedSpaceMap A R X Subtype.val
          A.isOpenEmbedding'.continuous)).inv ≫
          ContinuousFunctions.ringedSpaceMap A R X Subtype.val
            A.isOpenEmbedding'.continuous =
        (ContinuousFunctions.ringedSpace X R).ofRestrict A.isOpenEmbedding) := by
  letI := ContinuousFunctions.ringedSpaceMap_isOpenImmersion
    A X R Subtype.val A.isOpenEmbedding'
  exact SheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict
    (ContinuousFunctions.ringedSpaceMap A R X Subtype.val A.isOpenEmbedding'.continuous)

example : SheafedSpace.IsOpenImmersion
    (ContinuousFunctions.ringedSpaceMap (↥(⊥ : Opens X)) R X Subtype.val
      (⊥ : Opens X).isOpenEmbedding'.continuous) :=
  ContinuousFunctions.ringedSpaceMap_isOpenImmersion
    (↥(⊥ : Opens X)) X R Subtype.val (⊥ : Opens X).isOpenEmbedding'

example [Subsingleton R] (A : Opens X) : SheafedSpace.IsOpenImmersion
    (ContinuousFunctions.ringedSpaceMap A R X Subtype.val
      A.isOpenEmbedding'.continuous) :=
  ContinuousFunctions.ringedSpaceMap_isOpenImmersion A X R Subtype.val
    A.isOpenEmbedding'

end GeneralRing

section Integers

variable (X : Type) [TopologicalSpace X]

example (A : Opens X) [TopologicalSpace ℤ] [IsTopologicalRing ℤ] :
    SheafedSpace.IsOpenImmersion
      (ContinuousFunctions.ringedSpaceMap A ℤ X Subtype.val
        A.isOpenEmbedding'.continuous) :=
  ContinuousFunctions.ringedSpaceMap_isOpenImmersion A X ℤ Subtype.val
    A.isOpenEmbedding'

end Integers

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
