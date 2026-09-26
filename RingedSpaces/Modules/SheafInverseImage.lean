/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.PresheafInverseImageHom
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Topology.Sheaves.Functors

/-!
# Sheaf inverse image of modules

Sheafify the actual neighborhood-colimit module presheaf, compare the underlying
additive sheaf with ordinary inverse image, and transport its action across the
nonidentity comparison with the forgotten commutative-ring inverse-image sheaf.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- Filtered colimits commute with forgetting commutativity of ring presheaves. -/
noncomputable def commRingPointwiseComparison
    (R : Y.Presheaf CommRingCat.{v}) :
    (Opens.map f).op.pointwiseLeftKanExtension R ⋙
        forget₂ CommRingCat.{v} RingCat.{v} ≅
      (Opens.map f).op.pointwiseLeftKanExtension
        (R ⋙ forget₂ CommRingCat.{v} RingCat.{v}) := by
  letI (U : (Opens X)ᵒᵖ) : FinallySmall.{v} (index f (unop U)) :=
    finallySmall_of_essentiallySmall _
  letI (U : (Opens X)ᵒᵖ) :
      PreservesColimitsOfShape (index f (unop U))
        (forget₂ CommRingCat.{v} RingCat.{v}) :=
    FinallySmall.preservesColimitsOfShape_of_isFiltered
      (index f (unop U)) (forget₂ CommRingCat.{v} RingCat.{v})
  letI : (forget₂ CommRingCat.{v} RingCat.{v}).PreservesPointwiseLeftKanExtension
      R (Opens.map f).op := fun _ => inferInstance
  exact (forget₂ CommRingCat.{v} RingCat.{v}).pointwiseLeftKanExtensionCompIsoOfPreserves
    R (Opens.map f).op

/-- Compare ordinary commutative-ring and ring presheaf inverse images. -/
noncomputable def commRingPullbackComparison
    (R : Y.Presheaf CommRingCat.{v}) :
    (TopCat.Presheaf.pullback CommRingCat.{v} f).obj R ⋙
        forget₂ CommRingCat.{v} RingCat.{v} ≅
      (TopCat.Presheaf.pullback RingCat.{v} f).obj
        (R ⋙ forget₂ CommRingCat.{v} RingCat.{v}) :=
  Functor.isoWhiskerRight (pointwiseToPullback f CommRingCat.{v} R).symm
      (forget₂ CommRingCat.{v} RingCat.{v}) ≪≫
    commRingPointwiseComparison f R ≪≫
    pointwiseToPullback f RingCat.{v}
      (R ⋙ forget₂ CommRingCat.{v} RingCat.{v})

/-- Sheafify the ordinary ring presheaf inverse image. -/
noncomputable def inverseImageSheafRing (R : Y.Presheaf RingCat.{v}) :
    X.Sheaf RingCat.{v} :=
  (presheafToSheaf (Opens.grothendieckTopology X) RingCat.{v}).obj
    ((Opens.map f).op.pointwiseLeftKanExtension R)

/-- Sheafify the ordinary inverse-image module using the actual ring sheafification unit. -/
noncomputable def inverseImageSheafModule (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) :
    SheafOfModules.{v} (inverseImageSheafRing f R) :=
  (PresheafOfModules.sheafification
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((Opens.map f).op.pointwiseLeftKanExtension R))).obj (inverseImageModule f R M)

/-- The underlying additive sheaf is the sheafification of ordinary additive pullback. -/
noncomputable def inverseImageSheafUnderlying (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) :
    (⟨(inverseImageSheafModule f R M).val.presheaf,
      (inverseImageSheafModule f R M).isSheaf⟩ : X.Sheaf AddCommGrpCat.{v}) ≅
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
      ((TopCat.Presheaf.pullback AddCommGrpCat.{v} f).obj M.presheaf) :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).mapIso
    ((underlyingComparison f R).app M)

/-- Identify ring sheafification with the ordinary ring sheaf inverse image. -/
noncomputable def inverseImageSheafRingComparison (S : Y.Sheaf RingCat.{v}) :
    inverseImageSheafRing f S.obj ≅ (TopCat.Sheaf.pullback RingCat.{v} f).obj S :=
  (presheafToSheaf (Opens.grothendieckTopology X) RingCat.{v}).mapIso
      (pointwiseToPullback f RingCat.{v} S.obj) ≪≫
    ((TopCat.Sheaf.pullbackIso RingCat.{v} f).app S).symm

/-- For a module sheaf, recover the ordinary inverse-image additive sheaf. -/
noncomputable def inverseImageSheafUnderlyingOfSheaf (S : Y.Sheaf RingCat.{v})
    (M : SheafOfModules.{v} S) :
    (⟨(inverseImageSheafModule f S.obj M.val).val.presheaf,
      (inverseImageSheafModule f S.obj M.val).isSheaf⟩ : X.Sheaf AddCommGrpCat.{v}) ≅
    (TopCat.Sheaf.pullback AddCommGrpCat.{v} f).obj
      (⟨M.val.presheaf, M.isSheaf⟩ : Y.Sheaf AddCommGrpCat.{v}) :=
  inverseImageSheafUnderlying f S.obj M.val ≪≫
    ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} f).app
      (⟨M.val.presheaf, M.isSheaf⟩ : Y.Sheaf AddCommGrpCat.{v})).symm

/-- Transport the constructed sheaf module to the actual inverse-image ring sheaf. -/
noncomputable def inverseImageModuleOverActualRing (S : Y.Sheaf RingCat.{v})
    (M : PresheafOfModules.{v} S.obj) :
    SheafOfModules.{v} ((TopCat.Sheaf.pullback RingCat.{v} f).obj S) :=
  { val := (inverseImageSheafModule f S.obj M).val.restrictScalarsObj
      (inverseImageSheafRingComparison f S).inv.hom
    isSheaf := (inverseImageSheafModule f S.obj M).isSheaf }

/-- The transported module still has the ordinary additive inverse-image sheaf. -/
noncomputable def inverseImageModuleOverActualRingUnderlying (S : Y.Sheaf RingCat.{v})
    (M : SheafOfModules.{v} S) :
    (⟨(inverseImageModuleOverActualRing f S M.val).val.presheaf,
      (inverseImageModuleOverActualRing f S M.val).isSheaf⟩ : X.Sheaf AddCommGrpCat.{v}) ≅
    (TopCat.Sheaf.pullback AddCommGrpCat.{v} f).obj
      (⟨M.val.presheaf, M.isSheaf⟩ : Y.Sheaf AddCommGrpCat.{v}) :=
  inverseImageSheafUnderlyingOfSheaf f S M

end RingedSpaces.Modules.PresheafInverseImage

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

private instance ringHasSheafCompose (T : TopCat.{v}) :
    (Opens.grothendieckTopology T).HasSheafCompose
      (forget₂ CommRingCat.{v} RingCat.{v}) := by
  exact CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize _

private instance coverFinallySmall (T : TopCat.{v}) (U : Opens T) :
    FinallySmall.{v} ((Opens.grothendieckTopology T).Cover U)ᵒᵖ :=
  finallySmall_of_essentiallySmall _

private instance coverForgetPreserves (T : TopCat.{v}) (U : Opens T) :
    PreservesColimitsOfShape ((Opens.grothendieckTopology T).Cover U)ᵒᵖ
      (forget₂ CommRingCat.{v} RingCat.{v}) :=
  FinallySmall.preservesColimitsOfShape_of_isFiltered _ _

private instance ringPreservesSheafification (T : TopCat.{v}) :
    (Opens.grothendieckTopology T).PreservesSheafification
      (forget₂ CommRingCat.{v} RingCat.{v}) := by
  infer_instance

/-- The opens above an image have common refinements. This local witness is needed
for commutative-ring colimits: the presheaf module's witness is intentionally private. -/
private def commonIndex {U : Opens X} (i j : PresheafInverseImage.index f U) :
    PresheafInverseImage.index f U :=
  CostructuredArrow.mk <| (homOfLE (show U ≤
    (Opens.map f).obj (unop i.left ⊓ unop j.left) from
    le_inf (leOfHom i.hom.unop) (leOfHom j.hom.unop))).op

private instance {U : Opens X} : IsFiltered (PresheafInverseImage.index f U) where
  nonempty := ⟨CostructuredArrow.mk <| (homOfLE (show U ≤ (Opens.map f).obj ⊤ from
    by rw [Opens.map_top]; exact le_top)).op⟩
  cocone_objs i j := ⟨commonIndex f i j,
    CostructuredArrow.homMk (homOfLE inf_le_left).op,
    CostructuredArrow.homMk (homOfLE inf_le_right).op, trivial⟩
  cocone_maps {i j} α β := ⟨j, 𝟙 _, by
    apply CostructuredArrow.hom_ext
    apply Subsingleton.elim⟩

private instance indexFinallySmall (f : X ⟶ Y) (U : (Opens X)ᵒᵖ) :
    FinallySmall.{v} (PresheafInverseImage.index f (unop U)) :=
  finallySmall_of_essentiallySmall _

private instance indexForgetPreserves (f : X ⟶ Y) (U : (Opens X)ᵒᵖ) :
    PreservesColimitsOfShape (PresheafInverseImage.index f (unop U))
      (forget₂ CommRingCat.{v} RingCat.{v}) :=
  FinallySmall.preservesColimitsOfShape_of_isFiltered _ _

private instance pointwiseForgetPreserves (f : X ⟶ Y)
    (P : Y.Presheaf CommRingCat.{v}) :
    (forget₂ CommRingCat.{v} RingCat.{v}).PreservesPointwiseLeftKanExtension
      P (Opens.map f).op := fun _ => inferInstance

/-- Forget commutativity of a sheaf of rings, compatibly with its sheaf condition. -/
abbrev sheafForget (T : TopCat.{v}) :=
  sheafCompose (Opens.grothendieckTopology T) (forget₂ CommRingCat.{v} RingCat.{v})

set_option maxHeartbeats 1000000 in
theorem chosenUnitFac (A : Type (v+1)) [Category.{v} A]
    {FA : A → A → Type*} {CA : A → Type v}
    [∀ B C, FunLike (FA B C) (CA B) (CA C)] [ConcreteCategory.{v} A FA]
    [HasColimits A] [HasLimits A] [PreservesLimits (forget A)]
    [PreservesFilteredColimits (forget A)] [(forget A).ReflectsIsomorphisms]
    (S : Y.Sheaf A) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app S ≫
      (TopCat.Sheaf.pushforward A f).map
        ((TopCat.Sheaf.pullbackIso A f).hom.app S) =
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) A
       (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app S := by
  exact Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous (Opens.map f) A
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) A
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) S

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem constructedUnitFac (A : Type (v+1)) [Category.{v} A]
    {FA : A → A → Type*} {CA : A → Type v}
    [∀ B C, FunLike (FA B C) (CA B) (CA C)] [ConcreteCategory.{v} A FA]
    [HasColimits A] [HasLimits A] [PreservesLimits (forget A)]
    [PreservesFilteredColimits (forget A)] [(forget A).ReflectsIsomorphisms]
    (S : Y.Sheaf A) :
    (sheafToPresheaf (Opens.grothendieckTopology Y) A).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) A
         (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app S) =
    ((Opens.map f).op.leftKanExtensionUnit S.obj) ≫
      (Opens.map f).op.whiskerLeft
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback A f).obj S.obj)) := by
  dsimp only [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp [Adjunction.comp_unit_app, -ObjectProperty.ι_obj, -ObjectProperty.ι_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pointwiseToPullbackFac (C : Type (v + 1)) [Category.{v} C]
    [HasColimits C] (P : Y.Presheaf C) :
    (Opens.map f).op.pointwiseLeftKanExtensionUnit P ≫
      (Opens.map f).op.whiskerLeft
        (PresheafInverseImage.pointwiseToPullback f C P).hom =
      (Opens.map f).op.leftKanExtensionUnit P :=
  by
    simpa only [PresheafInverseImage.pointwiseToPullback,
      Functor.leftKanExtensionUnique, Functor.leftKanExtensionUniqueOfIso,
      Iso.refl_hom, Category.id_comp] using
      (Functor.descOfIsLeftKanExtension_fac
        (α := (Opens.map f).op.pointwiseLeftKanExtensionUnit P)
        (G := (Opens.map f).op.leftKanExtension P)
        (β := (Opens.map f).op.leftKanExtensionUnit P))

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem presheafComparisonFacApp (P : Y.Presheaf CommRingCat.{v})
    (V : (Opens Y)ᵒᵖ) :
    (forget₂ CommRingCat.{v} RingCat.{v}).map
        (((Opens.map f).op.leftKanExtensionUnit P).app V) ≫
      (PresheafInverseImage.commRingPullbackComparison f P).hom.app
        ((Opens.map f).op.obj V) =
    ((Opens.map f).op.leftKanExtensionUnit
      (P ⋙ forget₂ CommRingCat.{v} RingCat.{v})).app V := by
  simp only [PresheafInverseImage.commRingPullbackComparison,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom]
  let forget : CommRingCat.{v} ⥤ RingCat.{v} :=
    forget₂ CommRingCat.{v} RingCat.{v}
  have hC := NatTrans.congr_app
    (pointwiseToPullbackFac f CommRingCat.{v} P) V
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hC
  have hR := NatTrans.congr_app
    (pointwiseToPullbackFac f RingCat.{v} (P ⋙ forget)) V
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hR
  have hP := Functor.pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac_app
    forget P (Opens.map f).op V
  calc
    forget.map (((Opens.map f).op.leftKanExtensionUnit P).app V) ≫
        (Functor.whiskerRight (PresheafInverseImage.pointwiseToPullback f CommRingCat.{v} P).symm.hom forget).app ((Opens.map f).op.obj V) ≫
        (PresheafInverseImage.commRingPointwiseComparison f P).hom.app ((Opens.map f).op.obj V) ≫
        (PresheafInverseImage.pointwiseToPullback f RingCat.{v} (P ⋙ forget)).hom.app ((Opens.map f).op.obj V)
      = forget.map (((Opens.map f).op.pointwiseLeftKanExtensionUnit P).app V) ≫
        (PresheafInverseImage.commRingPointwiseComparison f P).hom.app ((Opens.map f).op.obj V) ≫
        (PresheafInverseImage.pointwiseToPullback f RingCat.{v} (P ⋙ forget)).hom.app ((Opens.map f).op.obj V) := by
          simp only [Functor.whiskerRight_app, Iso.symm_hom]
          simp only [← Functor.map_comp, ← Category.assoc]
          rw [← hC]
          simp
    _ = _ := by
      rw [← Category.assoc]
      change (forget.map (((Opens.map f).op.pointwiseLeftKanExtensionUnit P).app V) ≫
        (forget.pointwiseLeftKanExtensionCompIsoOfPreserves P (Opens.map f).op).hom.app ((Opens.map f).op.obj V)) ≫
        (PresheafInverseImage.pointwiseToPullback f RingCat.{v} (P ⋙ forget)).hom.app ((Opens.map f).op.obj V) = _
      rw [hP]
      exact hR

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem presheafComparisonFac (P : Y.Presheaf CommRingCat.{v}) :
    Functor.whiskerRight ((Opens.map f).op.leftKanExtensionUnit P)
      (forget₂ CommRingCat.{v} RingCat.{v}) ≫
      (Functor.associator (Opens.map f).op
        ((TopCat.Presheaf.pullback CommRingCat.{v} f).obj P)
        (forget₂ CommRingCat.{v} RingCat.{v})).hom ≫
      (Opens.map f).op.whiskerLeft
        (PresheafInverseImage.commRingPullbackComparison f P).hom =
    (Opens.map f).op.leftKanExtensionUnit
      (P ⋙ forget₂ CommRingCat.{v} RingCat.{v}) := by
  apply NatTrans.ext
  funext V
  change (forget₂ CommRingCat.{v} RingCat.{v}).map
      (((Opens.map f).op.leftKanExtensionUnit P).app V) ≫
      (PresheafInverseImage.commRingPullbackComparison f P).hom.app
        ((Opens.map f).op.obj V) =
    ((Opens.map f).op.leftKanExtensionUnit
      (P ⋙ forget₂ CommRingCat.{v} RingCat.{v})).app V
  exact presheafComparisonFacApp f P V

/-- Compare sheafification of the chosen commutative and ordinary ring pullbacks. -/
noncomputable def constructedComparison (S : Y.Sheaf CommRingCat.{v}) :
    (sheafForget X).obj
      ((presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{v}).obj
        ((TopCat.Presheaf.pullback CommRingCat.{v} f).obj S.obj)) ≅
    (presheafToSheaf (Opens.grothendieckTopology X) RingCat.{v}).obj
      ((TopCat.Presheaf.pullback RingCat.{v} f).obj
        ((sheafForget Y).obj S).obj) :=
  ((sheafComposeNatIso (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{v} RingCat.{v})
      (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{v})
      (sheafificationAdjunction (Opens.grothendieckTopology X) RingCat.{v})).app
      ((TopCat.Presheaf.pullback CommRingCat.{v} f).obj S.obj)).symm ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X) RingCat.{v}).mapIso
      (PresheafInverseImage.commRingPullbackComparison f S.obj)

/-- Canonical comparison of actual ordinary ring sheaf inverse images. -/
noncomputable def comparison (S : Y.Sheaf CommRingCat.{v}) :
    (sheafForget X).obj ((TopCat.Sheaf.pullback CommRingCat.{v} f).obj S) ≅
    (TopCat.Sheaf.pullback RingCat.{v} f).obj ((sheafForget Y).obj S) :=
  (sheafForget X).mapIso ((TopCat.Sheaf.pullbackIso CommRingCat.{v} f).app S) ≪≫
    constructedComparison f S ≪≫
    ((TopCat.Sheaf.pullbackIso RingCat.{v} f).app ((sheafForget Y).obj S)).symm

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem constructedComparison_sheafUnit (S : Y.Sheaf CommRingCat.{v}) :
    Functor.whiskerRight
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{v} f).obj S.obj))
        (forget₂ CommRingCat.{v} RingCat.{v}) ≫
      (sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{v}).map
        (constructedComparison f S).hom =
    (PresheafInverseImage.commRingPullbackComparison f S.obj).hom ≫
      toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback RingCat.{v} f).obj
          ((sheafForget Y).obj S).obj) := by
  simp only [constructedComparison, Iso.trans_hom, Functor.map_comp]
  change Functor.whiskerRight
      (toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback CommRingCat.{v} f).obj S.obj))
      (forget₂ CommRingCat.{v} RingCat.{v}) ≫
      (sheafifyComposeIso (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{v} RingCat.{v})
        ((TopCat.Presheaf.pullback CommRingCat.{v} f).obj S.obj)).inv ≫
      sheafifyMap (Opens.grothendieckTopology X)
        (PresheafInverseImage.commRingPullbackComparison f S.obj).hom = _
  rw [← Category.assoc, sheafComposeIso_inv_fac]
  exact (toSheafify_naturality (Opens.grothendieckTopology X)
    (PresheafInverseImage.commRingPullbackComparison f S.obj).hom).symm

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem constructedComparison_unit (S : Y.Sheaf CommRingCat.{v}) :
    (sheafForget Y).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
          CommRingCat.{v} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app S) ≫
      (TopCat.Sheaf.pushforward RingCat.{v} f).map
        (constructedComparison f S).hom =
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
      RingCat.{v} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)).unit.app ((sheafForget Y).obj S) := by
  apply (sheafToPresheaf (Opens.grothendieckTopology Y) RingCat.{v}).map_injective
  apply NatTrans.ext
  funext V
  change (forget₂ CommRingCat.{v} RingCat.{v}).map
      (((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{v}).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
            CommRingCat.{v} (Opens.grothendieckTopology Y)
            (Opens.grothendieckTopology X)).unit.app S)).app V) ≫
    ((sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{v}).map
      (constructedComparison f S).hom).app ((Opens.map f).op.obj V) =
    ((sheafToPresheaf (Opens.grothendieckTopology Y) RingCat.{v}).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
        RingCat.{v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app ((sheafForget Y).obj S))).app V
  have hC := NatTrans.congr_app (constructedUnitFac f CommRingCat.{v} S) V
  have hR := NatTrans.congr_app (constructedUnitFac f RingCat.{v} ((sheafForget Y).obj S)) V
  rw [hC, hR]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  have hS := NatTrans.congr_app (constructedComparison_sheafUnit f S)
    ((Opens.map f).op.obj V)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hS
  rw [hS, ← Category.assoc, presheafComparisonFacApp f S.obj V]
  rfl

theorem pushforwardForget_map {A B : X.Sheaf CommRingCat.{v}} (t : A ⟶ B) :
    (sheafForget Y).map ((TopCat.Sheaf.pushforward CommRingCat.{v} f).map t) =
      (TopCat.Sheaf.pushforward RingCat.{v} f).map ((sheafForget X).map t) :=
  rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem comparison_unit (S : Y.Sheaf CommRingCat.{v}) :
    (sheafForget Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f).unit.app S) ≫
      (TopCat.Sheaf.pushforward RingCat.{v} f).map (comparison f S).hom =
    (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{v} f).unit.app
      ((sheafForget Y).obj S) := by
  have hC := congrArg (fun t => (sheafForget Y).map t)
    (chosenUnitFac f CommRingCat.{v} S)
  simp only [Functor.map_comp] at hC
  rw [pushforwardForget_map] at hC
  have hR := chosenUnitFac f RingCat.{v} ((sheafForget Y).obj S)
  simp only [comparison, Iso.trans_hom, Functor.map_comp]
  change (sheafForget Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f).unit.app S) ≫
      (TopCat.Sheaf.pushforward RingCat.{v} f).map
        ((sheafForget X).map ((TopCat.Sheaf.pullbackIso CommRingCat.{v} f).hom.app S)) ≫
      (TopCat.Sheaf.pushforward RingCat.{v} f).map (constructedComparison f S).hom ≫
      (TopCat.Sheaf.pushforward RingCat.{v} f).map
        ((TopCat.Sheaf.pullbackIso RingCat.{v} f).app ((sheafForget Y).obj S)).inv =
    (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{v} f).unit.app
      ((sheafForget Y).obj S)
  calc
    _ = (sheafForget Y).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
            CommRingCat.{v} (Opens.grothendieckTopology Y)
            (Opens.grothendieckTopology X)).unit.app S) ≫
        (TopCat.Sheaf.pushforward RingCat.{v} f).map
          (constructedComparison f S).hom ≫
        (TopCat.Sheaf.pushforward RingCat.{v} f).map
          ((TopCat.Sheaf.pullbackIso RingCat.{v} f).app ((sheafForget Y).obj S)).inv := by
            rw [← Category.assoc, hC]
    _ = (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
          RingCat.{v} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app ((sheafForget Y).obj S) ≫
        (TopCat.Sheaf.pushforward RingCat.{v} f).map
          ((TopCat.Sheaf.pullbackIso RingCat.{v} f).app ((sheafForget Y).obj S)).inv := by
            rw [← Category.assoc, constructedComparison_unit f S]
    _ = _ := by
      rw [← hR, Category.assoc, ← Functor.map_comp,
        show ((TopCat.Sheaf.pullbackIso RingCat.{v} f).hom.app
          ((sheafForget Y).obj S)) =
          ((TopCat.Sheaf.pullbackIso RingCat.{v} f).app
            ((sheafForget Y).obj S)).hom from rfl,
        Iso.hom_inv_id]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem comparison_unit_inv (S : Y.Sheaf CommRingCat.{v}) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{v} f).unit.app
        ((sheafForget Y).obj S) ≫
      (TopCat.Sheaf.pushforward RingCat.{v} f).map (comparison f S).inv =
    (sheafForget Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f).unit.app S) := by
  calc
    _ = ((sheafForget Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f).unit.app S) ≫
        (TopCat.Sheaf.pushforward RingCat.{v} f).map (comparison f S).hom) ≫
        (TopCat.Sheaf.pushforward RingCat.{v} f).map (comparison f S).inv := by
      rw [comparison_unit f S]
    _ = _ := by
      rw [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
      rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem comparison_naturality {S T : Y.Sheaf CommRingCat.{v}} (t : S ⟶ T) :
    (sheafForget X).map ((TopCat.Sheaf.pullback CommRingCat.{v} f).map t) ≫
      (comparison f T).hom =
      (comparison f S).hom ≫ (TopCat.Sheaf.pullback RingCat.{v} f).map
      ((sheafForget Y).map t) := by
  have h : (comparison f S).inv ≫
        (sheafForget X).map ((TopCat.Sheaf.pullback CommRingCat.{v} f).map t) ≫
          (comparison f T).hom =
      (TopCat.Sheaf.pullback RingCat.{v} f).map ((sheafForget Y).map t) := by
    apply ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{v} f).homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    have hC := congrArg (fun s => (sheafForget Y).map s)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f).unit.naturality t)
    simp only [Functor.map_comp, Functor.comp_map, Functor.id_map] at hC
    have hR :=
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{v} f).unit.naturality
        ((sheafForget Y).map t)
    simp only [Functor.comp_map, Functor.id_map] at hR
    simp only [← Category.assoc]
    rw [comparison_unit_inv f S,
      ← pushforwardForget_map f ((TopCat.Sheaf.pullback CommRingCat.{v} f).map t)]
    rw [← hC, Category.assoc, comparison_unit f T]
    exact hR
  have h' := congrArg (fun k => (comparison f S).hom ≫ k) h
  rw [← Category.assoc] at h'
  rw [Iso.hom_inv_id] at h'
  simpa only [Category.id_comp] using h'

/-- Naturality of the canonical comparison in the whole ring sheaf. -/
noncomputable def comparisonNatIso :
    TopCat.Sheaf.pullback CommRingCat.{v} f ⋙ sheafForget X ≅
    sheafForget Y ⋙ TopCat.Sheaf.pullback RingCat.{v} f :=
  NatIso.ofComponents (comparison f) (fun _ => comparison_naturality f _)

theorem comparison_unit_app (S : Y.Sheaf CommRingCat.{v})
    (V : (Opens Y)ᵒᵖ) :
    (forget₂ CommRingCat.{v} RingCat.{v}).map
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f).unit.app S).hom.app V) ≫
      (comparison f S).hom.hom.app ((Opens.map f).op.obj V) =
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{v} f).unit.app
      ((sheafForget Y).obj S)).hom.app V := by
  have h := comparison_unit f S
  exact NatTrans.congr_app (congrArg (fun t => t.hom) h) V

/-- Transport the accepted inverse-image action along the ordinary ring comparison. -/
noncomputable def module (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} ((sheafForget Y).obj S)) :
    SheafOfModules.{v} ((sheafForget X).obj
      ((TopCat.Sheaf.pullback CommRingCat.{v} f).obj S)) :=
  { val := (PresheafInverseImage.inverseImageModuleOverActualRing f
        ((sheafForget Y).obj S) M.val).val.restrictScalarsObj
        (comparison f S).hom.hom
    isSheaf := (PresheafInverseImage.inverseImageModuleOverActualRing f
      ((sheafForget Y).obj S) M.val).isSheaf }

/-- Retain the full additive ordinary-inverse-image sheaf isomorphism. -/
noncomputable def moduleUnderlying (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} ((sheafForget Y).obj S)) :
    (⟨(module f S M).val.presheaf,
      (module f S M).isSheaf⟩ : X.Sheaf AddCommGrpCat.{v}) ≅
    (TopCat.Sheaf.pullback AddCommGrpCat.{v} f).obj
      (⟨M.val.presheaf, M.isSheaf⟩ : Y.Sheaf AddCommGrpCat.{v}) :=
  PresheafInverseImage.inverseImageModuleOverActualRingUnderlying f
    ((sheafForget Y).obj S) M

/-- The additive module map obtained from the native unit and inverse underlying iso. -/
noncomputable def moduleUnit (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} ((sheafForget Y).obj S)) :
    (⟨M.val.presheaf, M.isSheaf⟩ : Y.Sheaf AddCommGrpCat.{v}) ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).obj
      (⟨(module f S M).val.presheaf,
        (module f S M).isSheaf⟩ : X.Sheaf AddCommGrpCat.{v}) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).unit.app
      (⟨M.val.presheaf, M.isSheaf⟩ : Y.Sheaf AddCommGrpCat.{v}) ≫
    (TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).map
      (moduleUnderlying f S M).inv

/-- The pointwise Kan unit followed by the sheafification unit, as a sheaf map. -/
noncomputable def pointwiseSheafUnit (A : Type (v + 1)) [Category.{v} A]
    {FA : A → A → Type*} {CA : A → Type v}
    [∀ B C, FunLike (FA B C) (CA B) (CA C)] [ConcreteCategory.{v} A FA]
    [HasColimits A] [HasLimits A] [PreservesLimits (forget A)]
    [PreservesFilteredColimits (forget A)] [(forget A).ReflectsIsomorphisms]
    (S : Y.Sheaf A) :
    S ⟶ (TopCat.Sheaf.pushforward A f).obj
      ((presheafToSheaf (Opens.grothendieckTopology X) A).obj
        ((Opens.map f).op.pointwiseLeftKanExtension S.obj)) :=
  ⟨(Opens.map f).op.pointwiseLeftKanExtensionUnit S.obj ≫
    (Opens.map f).op.whiskerLeft
      (toSheafify (Opens.grothendieckTopology X)
        ((Opens.map f).op.pointwiseLeftKanExtension S.obj))⟩

set_option backward.isDefEq.respectTransparency false in
theorem pointwiseSheafUnit_fac (A : Type (v + 1)) [Category.{v} A]
    {FA : A → A → Type*} {CA : A → Type v}
    [∀ B C, FunLike (FA B C) (CA B) (CA C)] [ConcreteCategory.{v} A FA]
    [HasColimits A] [HasLimits A] [PreservesLimits (forget A)]
    [PreservesFilteredColimits (forget A)] [(forget A).ReflectsIsomorphisms]
    (S : Y.Sheaf A) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction A f).unit.app S ≫
      (TopCat.Sheaf.pushforward A f).map
        ((TopCat.Sheaf.pullbackIso A f).hom.app S) ≫
      (TopCat.Sheaf.pushforward A f).map
        ((presheafToSheaf (Opens.grothendieckTopology X) A).mapIso
          (PresheafInverseImage.pointwiseToPullback f A S.obj)).inv =
    pointwiseSheafUnit f A S := by
  rw [← Category.assoc, chosenUnitFac f A S]
  apply (sheafToPresheaf (Opens.grothendieckTopology Y) A).map_injective
  rw [Functor.map_comp, constructedUnitFac f A S]
  change
    ((Opens.map f).op.leftKanExtensionUnit S.obj ≫
      (Opens.map f).op.whiskerLeft
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback A f).obj S.obj))) ≫
      (Opens.map f).op.whiskerLeft
        (sheafifyMap (Opens.grothendieckTopology X)
          (PresheafInverseImage.pointwiseToPullback f A S.obj).inv) =
    (Opens.map f).op.pointwiseLeftKanExtensionUnit S.obj ≫
      (Opens.map f).op.whiskerLeft
        (toSheafify (Opens.grothendieckTopology X)
          ((Opens.map f).op.pointwiseLeftKanExtension S.obj))
  rw [Category.assoc, ← Functor.whiskerLeft_comp]
  have hs := (toSheafify_naturality (Opens.grothendieckTopology X)
    (PresheafInverseImage.pointwiseToPullback f A S.obj).inv).symm
  rw [hs]
  rw [Functor.whiskerLeft_comp]
  have hp : (Opens.map f).op.leftKanExtensionUnit S.obj ≫
      (Opens.map f).op.whiskerLeft
        (PresheafInverseImage.pointwiseToPullback f A S.obj).inv =
      (Opens.map f).op.pointwiseLeftKanExtensionUnit S.obj := by
    rw [← pointwiseToPullbackFac f A S.obj, Category.assoc,
      ← Functor.whiskerLeft_comp, Iso.hom_inv_id]
    simp
  rw [← Category.assoc, hp]

theorem moduleUnderlying_inv_eq (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} ((sheafForget Y).obj S)) :
    (moduleUnderlying f S M).inv =
      ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} f).hom.app
        (⟨M.val.presheaf, M.isSheaf⟩ : Y.Sheaf AddCommGrpCat.{v})) ≫
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).mapIso
        (PresheafInverseImage.pointwiseToPullback f AddCommGrpCat.{v}
          M.val.presheaf)).inv := by
  rfl

theorem ringComparison_inv_eq (S : Y.Sheaf RingCat.{v}) :
    (PresheafInverseImage.inverseImageSheafRingComparison f S).inv =
      ((TopCat.Sheaf.pullbackIso RingCat.{v} f).hom.app S) ≫
      ((presheafToSheaf (Opens.grothendieckTopology X) RingCat.{v}).mapIso
        (PresheafInverseImage.pointwiseToPullback f RingCat.{v} S.obj)).inv := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem ringUnit_pointwise (S : Y.Sheaf RingCat.{v}) (V : (Opens Y)ᵒᵖ)
    (r : S.obj.obj V) :
    (PresheafInverseImage.inverseImageSheafRingComparison f S).inv.hom.app
        ((Opens.map f).op.obj V)
        (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{v} f).unit.app S).hom.app V r) =
      (toSheafify (Opens.grothendieckTopology X)
        ((Opens.map f).op.pointwiseLeftKanExtension S.obj)).app
          ((Opens.map f).op.obj V)
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit S.obj).app V r) := by
  have h : (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{v} f).unit.app S ≫
        (TopCat.Sheaf.pushforward RingCat.{v} f).map
          (PresheafInverseImage.inverseImageSheafRingComparison f S).inv =
      pointwiseSheafUnit f RingCat.{v} S := by
    rw [ringComparison_inv_eq f S, Functor.map_comp]
    exact pointwiseSheafUnit_fac f RingCat.{v} S
  have h' := NatTrans.congr_app (congrArg (fun t => t.hom) h) V
  have h'' := congrArg (fun t => t r) h'
  convert h'' using 1 <;> rfl

/-- The transported inverse-image action on a pushed-forward module section. -/
noncomputable instance moduleTargetInstance (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} ((sheafForget Y).obj S)) (V : Opens Y) :
    Module
      (((sheafForget Y).obj ((TopCat.Sheaf.pushforward CommRingCat.{v} f).obj
        ((TopCat.Sheaf.pullback CommRingCat.{v} f).obj S))).obj.obj (op V))
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).obj
        (⟨(module f S M).val.presheaf,
          (module f S M).isSheaf⟩ : X.Sheaf AddCommGrpCat.{v})).obj.obj (op V)) :=
  inferInstanceAs (Module
    (((sheafForget X).obj ((TopCat.Sheaf.pullback CommRingCat.{v} f).obj S)).obj.obj
      (op ((Opens.map f).obj V)))
    ((module f S M).val.presheaf.obj (op ((Opens.map f).obj V))))

/-- The sectionwise action of the transported module over the pushed-forward ring. -/
noncomputable def transportedAction (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} ((sheafForget Y).obj S)) (V : Opens Y)
    (r : (((sheafForget Y).obj ((TopCat.Sheaf.pushforward CommRingCat.{v} f).obj
        ((TopCat.Sheaf.pullback CommRingCat.{v} f).obj S))).obj.obj (op V)))
    (m : (((TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).obj
        (⟨(module f S M).val.presheaf,
          (module f S M).isSheaf⟩ : X.Sheaf AddCommGrpCat.{v})).obj.obj (op V))) :=
  letI := moduleTargetInstance f S M V
  r • m

set_option backward.isDefEq.respectTransparency false in
theorem moduleUnit_pointwise (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} ((sheafForget Y).obj S)) (V : (Opens Y)ᵒᵖ)
    (m : M.val.obj V) :
    (moduleUnit f S M).hom.app V m =
      (toSheafify (Opens.grothendieckTopology X)
        ((Opens.map f).op.pointwiseLeftKanExtension M.val.presheaf)).app
          ((Opens.map f).op.obj V)
        (((Opens.map f).op.pointwiseLeftKanExtensionUnit M.val.presheaf).app V m) := by
  let underlying : Y.Sheaf AddCommGrpCat.{v} := ⟨M.val.presheaf, M.isSheaf⟩
  have h : moduleUnit f S M = pointwiseSheafUnit f AddCommGrpCat.{v} underlying := by
    change (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).unit.app
        underlying ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).map
        (moduleUnderlying f S M).inv = _
    rw [moduleUnderlying_inv_eq f S M, Functor.map_comp]
    exact pointwiseSheafUnit_fac f AddCommGrpCat.{v} underlying
  rw [h]
  rfl

set_option maxHeartbeats 1000000 in
theorem moduleUnit_smul (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} ((sheafForget Y).obj S)) (V : Opens Y)
    (r : ((sheafForget Y).obj S).obj.obj (op V))
    (m : M.val.obj (op V)) :
    (moduleUnit f S M).hom.app (op V) (r • m) =
      transportedAction f S M V (((sheafForget Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f).unit.app S)).hom.app
          (op V) r) ((moduleUnit f S M).hom.app (op V) m) := by
  let R₀ := (Opens.map f).op.pointwiseLeftKanExtension ((sheafForget Y).obj S).obj
  let N₀ := PresheafInverseImage.inverseImageModule f ((sheafForget Y).obj S).obj M.val
  let α := toSheafify (Opens.grothendieckTopology X) R₀
  let φ := toSheafify (Opens.grothendieckTopology X) N₀.presheaf
  let W : (Opens X)ᵒᵖ := (Opens.map f).op.obj (op V)
  let r₀ := ((Opens.map f).op.pointwiseLeftKanExtensionUnit ((sheafForget Y).obj S).obj).app (op V) r
  let m₀ := ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.val.presheaf).app (op V) m
  have hh := ((PresheafOfModules.toSheafify α φ).app W).hom.map_smul r₀ m₀
  have hRing :
      (PresheafInverseImage.inverseImageSheafRingComparison f
          ((sheafForget Y).obj S)).inv.hom.app W
        ((comparison f S).hom.hom.app W
          (((sheafForget Y).map
            ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f).unit.app S)).hom.app
              (op V) r)) = α.app W r₀ := by
    have hComp := congrArg (fun t => t r) (comparison_unit_app f S (op V))
    have hComp' :
        (comparison f S).hom.hom.app W
          (((sheafForget Y).map
            ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f).unit.app S)).hom.app
              (op V) r) =
        (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{v} f).unit.app
          ((sheafForget Y).obj S)).hom.app (op V) r) := by
      convert hComp using 1; rfl
    have hPart := congrArg (fun t =>
      (PresheafInverseImage.inverseImageSheafRingComparison f
        ((sheafForget Y).obj S)).inv.hom.app W t) hComp'
    convert hPart.trans (ringUnit_pointwise f ((sheafForget Y).obj S) (op V) r)
      using 1
  rw [moduleUnit_pointwise f S M (op V) (r • m), moduleUnit_pointwise f S M (op V) m]
  have hunit := PresheafInverseImage.unit_smul f ((sheafForget Y).obj S).obj
    M.val (op V) r m
  rw [← hunit]
  change ((PresheafOfModules.toSheafify α φ).app W).hom
    (PresheafInverseImage.pointwiseSmul f ((sheafForget Y).obj S).obj
      M.val ((Opens.map f).obj V) r₀ m₀) = _
  refine hh.trans ?_
  change PresheafOfModules.Sheafify.smul α φ (α.app W r₀) (φ.app W m₀) = _
  rw [← hRing]
  rfl

/-- The sheaf-module morphism functor assembled from native sheafification and scalar restriction. -/
noncomputable def moduleFunctor (S : Y.Sheaf CommRingCat.{v}) :
    SheafOfModules.{v} ((sheafForget Y).obj S) ⥤
      SheafOfModules.{v} ((sheafForget X).obj
        ((TopCat.Sheaf.pullback CommRingCat.{v} f).obj S)) :=
  SheafOfModules.forget ((sheafForget Y).obj S) ⋙
    PresheafInverseImage.inverseImageFunctor f ((sheafForget Y).obj S).obj ⋙
    PresheafOfModules.sheafification
      (toSheafify (Opens.grothendieckTopology X)
        ((Opens.map f).op.pointwiseLeftKanExtension ((sheafForget Y).obj S).obj)) ⋙
    SheafOfModules.restrictScalars
      ((comparison f S).hom ≫
        (PresheafInverseImage.inverseImageSheafRingComparison f
          ((sheafForget Y).obj S)).inv)

/-- The functor agrees definitionally with the transported object construction. -/
theorem moduleFunctor_obj (S : Y.Sheaf CommRingCat.{v})
    (M : SheafOfModules.{v} ((sheafForget Y).obj S)) :
    (moduleFunctor f S).obj M = module f S M := by
  rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Natural additive ordinary inverse-image isomorphism for the transported module functor. -/
noncomputable def moduleUnderlyingNatIso (S : Y.Sheaf CommRingCat.{v}) :
    moduleFunctor f S ⋙
      SheafOfModules.toSheaf ((sheafForget X).obj
        ((TopCat.Sheaf.pullback CommRingCat.{v} f).obj S)) ≅
    SheafOfModules.toSheaf ((sheafForget Y).obj S) ⋙
      TopCat.Sheaf.pullback AddCommGrpCat.{v} f :=
  NatIso.ofComponents (moduleUnderlying f S) (fun {M N} g => by
    simp only [Functor.comp_map, moduleFunctor, moduleUnderlying,
      PresheafInverseImage.inverseImageModuleOverActualRingUnderlying,
      PresheafInverseImage.inverseImageSheafUnderlyingOfSheaf,
      PresheafInverseImage.inverseImageSheafUnderlying,
      Iso.trans_hom, Functor.mapIso_hom]
    have hs := congrArg
      (fun t => (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).map t)
      ((PresheafInverseImage.underlyingComparison f ((sheafForget Y).obj S).obj).hom.naturality g.val)
    simp only [Functor.map_comp] at hs
    have hi := (TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} f).inv.naturality
      ((SheafOfModules.toSheaf ((sheafForget Y).obj S)).map g)
    have hleft :
        (SheafOfModules.toSheaf ((sheafForget X).obj
          ((TopCat.Sheaf.pullback CommRingCat.{v} f).obj S))).map
          ((SheafOfModules.restrictScalars
            ((comparison f S).hom ≫
              (PresheafInverseImage.inverseImageSheafRingComparison f
                ((sheafForget Y).obj S)).inv)).map
            ((PresheafOfModules.sheafification
              (toSheafify (Opens.grothendieckTopology X)
                ((Opens.map f).op.pointwiseLeftKanExtension
                  ((sheafForget Y).obj S).obj))).map
                ((PresheafInverseImage.inverseImageFunctor f
                  ((sheafForget Y).obj S).obj).map g.val))) =
          (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).map
            ((PresheafInverseImage.inverseImageFunctor f
              ((sheafForget Y).obj S).obj ⋙ PresheafOfModules.toPresheaf _).map g.val) := by
      rfl
    simp only [SheafOfModules.forget_map]
    have hchosen :
        (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).map
            ((PresheafOfModules.toPresheaf ((sheafForget Y).obj S).obj ⋙
              TopCat.Presheaf.pullback AddCommGrpCat.{v} f).map g.val) ≫
          (TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} f).inv.app
            ((SheafOfModules.toSheaf ((sheafForget Y).obj S)).obj N) =
        (TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} f).inv.app
            ((SheafOfModules.toSheaf ((sheafForget Y).obj S)).obj M) ≫
          (TopCat.Sheaf.pullback AddCommGrpCat.{v} f).map
            ((SheafOfModules.toSheaf ((sheafForget Y).obj S)).map g) := by
      convert hi using 1; rfl
    have hn := congrArg (fun t => t ≫
      (TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} f).inv.app
        ((SheafOfModules.toSheaf ((sheafForget Y).obj S)).obj N)) hs
    simp only [Category.assoc] at hn
    rw [hchosen] at hn
    convert hn using 1 <;> rfl)

end RingedSpaces.Modules.SheafInverseImage

#lint
