/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.PresheafInverseImage

/-!
# Direct-import clients for inverse-image module presheaves

All equations refer to the actual pointwise Kan extensions and their unit.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace
open RingedSpaces.Modules.PresheafInverseImage

namespace Test.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})
  (M : PresheafOfModules.{v} R)

theorem simultaneousGenerators (U : Opens X)
    (r : ((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U))
    (m : ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) :
    ∃ (i : index f U) (a : R.obj i.left) (b : M.obj i.left),
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) i) a = r ∧
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) b = m :=
  pointwise_jointly_surjective f R M U r m

theorem generatorAction (U : Opens X) (i : index f U)
    (a : R.obj i.left) (b : M.obj i.left) :
    pointwiseSmul f R M U
        ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) i) a)
        ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) b) =
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i)
        (a • b) :=
  pointwiseSmul_eq f R M U i a b

theorem ringRestrictionGenerator {U V : Opens X} (g : op U ⟶ op V)
    (i : index f U) (a : R.obj i.left) :
    ((Opens.map f).op.pointwiseLeftKanExtension R).map g
        ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) i) a) =
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op V) ⋙ R)
        ((CostructuredArrow.map g).obj i)) a :=
  ring_map_ι f R g i a

theorem moduleRestrictionGenerator {U V : Opens X} (g : op U ⟶ op V)
    (i : index f U) (b : M.obj i.left) :
    (inverseImageModule f R M).map g
        ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) b) =
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op V) ⋙ M.presheaf)
        ((CostructuredArrow.map g).obj i)) b :=
  group_map_ι f R M g i b

theorem restrictionArbitraryScalar {U V : Opens X} (g : op U ⟶ op V)
    (r : ((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U))
    (m : ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) :
    letI := pointwiseModule f R M U
    letI := pointwiseModule f R M V
    (inverseImageModule f R M).map g (r • m) =
      ((Opens.map f).op.pointwiseLeftKanExtension R).map g r •
        (inverseImageModule f R M).map g m := by
  exact restriction_smul f R M g r m

theorem restrictionIdentityComposition {U V W : Opens X}
    (g : op U ⟶ op V) (h : op V ⟶ op W) (m : (inverseImageModule f R M).obj (op U)) :
    (inverseImageModule f R M).map (𝟙 (op U)) m = m ∧
      (inverseImageModule f R M).map (g ≫ h) m =
        (inverseImageModule f R M).map h ((inverseImageModule f R M).map g m) := by
  constructor
  · rw [PresheafOfModules.map_id]
    rfl
  · exact (inverseImageModule f R M).map_comp_apply g h m

theorem inducedMapGenerator {N : PresheafOfModules.{v} R} (φ : M ⟶ N)
    (U : Opens X) (i : index f U) (b : M.obj i.left) :
    ((inverseImageFunctor f R).map φ).app (op U)
        ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) b) =
      (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ N.presheaf) i)
        (φ.app i.left b) :=
  pointwiseMap_ι f φ U i b

theorem inducedMapArbitraryScalar {N : PresheafOfModules.{v} R} (φ : M ⟶ N)
    (U : Opens X)
    (r : ((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U))
    (m : ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) :
    letI := pointwiseModule f R M U
    letI := pointwiseModule f R N U
    ((inverseImageFunctor f R).map φ).app (op U) (r • m) =
      r • ((inverseImageFunctor f R).map φ).app (op U) m := by
  exact pointwiseMap_smul f φ U r m

theorem inducedMapNaturality {N : PresheafOfModules.{v} R} (φ : M ⟶ N)
    {U V : Opens X} (g : op U ⟶ op V)
    (m : (inverseImageModule f R M).obj (op U)) :
    ((inverseImageFunctor f R).map φ).app (op V)
        ((inverseImageModule f R M).map g m) =
      (inverseImageModule f R N).map g
        (((inverseImageFunctor f R).map φ).app (op U) m) :=
  PresheafOfModules.naturality_apply ((inverseImageFunctor f R).map φ) g m

theorem inducedFunctorLaws {N P : PresheafOfModules.{v} R}
    (φ : M ⟶ N) (ψ : N ⟶ P) :
    (inverseImageFunctor f R).map (𝟙 M) =
        𝟙 ((inverseImageFunctor f R).obj M) ∧
      (inverseImageFunctor f R).map (φ ≫ ψ) =
        (inverseImageFunctor f R).map φ ≫ (inverseImageFunctor f R).map ψ :=
  ⟨(inverseImageFunctor f R).map_id M, (inverseImageFunctor f R).map_comp φ ψ⟩

theorem actualUnitAction (V : (Opens Y)ᵒᵖ) (a : R.obj V) (b : M.obj V) :
    pointwiseSmul f R M ((Opens.map f).obj (unop V))
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit R).app V a)
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V b) =
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V (a • b) :=
  unit_smul f R M V a b

theorem actualUnitNaturality {N : PresheafOfModules.{v} R} (φ : M ⟶ N) :
    (Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf ≫
        (Opens.map f).op.whiskerLeft (pointwiseMap f φ) =
      (PresheafOfModules.toPresheaf R).map φ ≫
        (Opens.map f).op.pointwiseLeftKanExtensionUnit N.presheaf :=
  pointwiseMap_unit f φ

theorem additiveComparisonNatural {N : PresheafOfModules.{v} R} (φ : M ⟶ N) :
    pointwiseMap f φ ≫ (underlyingComparison f R).hom.app N =
      (underlyingComparison f R).hom.app M ≫
        ((TopCat.Presheaf.pullback AddCommGrpCat.{v} f).map
          ((PresheafOfModules.toPresheaf R).map φ)) :=
  (underlyingComparison f R).hom.naturality φ

theorem additiveComparisonUnit :
    (Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf ≫
        (Opens.map f).op.whiskerLeft ((underlyingComparison f R).hom.app M) =
      (Opens.map f).op.leftKanExtensionUnit M.presheaf :=
  pointwiseToPullback_fac f M.presheaf

end Test.PresheafInverseImage
