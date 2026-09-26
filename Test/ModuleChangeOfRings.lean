/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.PresheafChangeOfRings
public import RingedSpaces.Modules.SheafChangeOfRings
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Direct-import change-of-rings clients

These tests exercise maps, naturality, units, counits and sectionwise scalars
on arbitrary sites, including sites without objects or sections.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v₁ u₁

namespace Test.ModuleChangeOfRings

variable {C : Type u₁} [Category.{v₁} C]
  (A B : Cᵒᵖ ⥤ CommRingCat.{u}) (theta : A ⟶ B)

theorem fullRingNaturality {U V : Cᵒᵖ} (f : U ⟶ V) (a : A.obj U) :
    theta.app V (A.map f a) = B.map f (theta.app U a) := by
  exact congrArg (fun h : A.obj U ⟶ B.obj V => h a) (theta.naturality f)

theorem nontrivialArrowRestriction (M : RingedSpaces.Modules.Presheaves A)
    {U V : Cᵒᵖ} (f : U ⟶ V) (b : B.obj U) (m : M.obj U) :
    (RingedSpaces.Modules.tensorPresheaf A B theta M).map f
        (b • RingedSpaces.Modules.tensorUnitSection A B theta M U m) =
      B.map f b • RingedSpaces.Modules.tensorUnitSection A B theta M V (M.map f m) := by
  exact RingedSpaces.Modules.tensorRestriction_smul A B theta M f b m

theorem tensorMapArbitraryScalar {M N : RingedSpaces.Modules.Presheaves A}
    (h : M ⟶ N) (U : Cᵒᵖ) (b : B.obj U) (m : M.obj U) :
    ((RingedSpaces.Modules.tensorPresheafFunctor A B theta).map h).app U
        (b • RingedSpaces.Modules.tensorUnitSection A B theta M U m) =
      b • RingedSpaces.Modules.tensorUnitSection A B theta N U (h.app U m) := by
  exact RingedSpaces.Modules.tensorSectionMap_smul A B theta h U b m

theorem tensorFunctorIdentityComposition
    {M N P : RingedSpaces.Modules.Presheaves A} (h : M ⟶ N) (k : N ⟶ P) :
    (RingedSpaces.Modules.tensorPresheafFunctor A B theta).map (𝟙 M) =
        𝟙 ((RingedSpaces.Modules.tensorPresheafFunctor A B theta).obj M) ∧
      (RingedSpaces.Modules.tensorPresheafFunctor A B theta).map (h ≫ k) =
        (RingedSpaces.Modules.tensorPresheafFunctor A B theta).map h ≫
          (RingedSpaces.Modules.tensorPresheafFunctor A B theta).map k :=
  ⟨(RingedSpaces.Modules.tensorPresheafFunctor A B theta).map_id M,
    (RingedSpaces.Modules.tensorPresheafFunctor A B theta).map_comp h k⟩

theorem homInverses (M : RingedSpaces.Modules.Presheaves A)
    (N : RingedSpaces.Modules.Presheaves B)
    (t : RingedSpaces.Modules.tensorPresheaf A B theta M ⟶ N)
    (g : M ⟶ (PresheafOfModules.restrictScalars
      (RingedSpaces.Modules.ringMap A B theta)).obj N) :
    (RingedSpaces.Modules.tensorPresheafHomEquiv A B theta M N).symm
        ((RingedSpaces.Modules.tensorPresheafHomEquiv A B theta M N) t) = t ∧
      (RingedSpaces.Modules.tensorPresheafHomEquiv A B theta M N)
        ((RingedSpaces.Modules.tensorPresheafHomEquiv A B theta M N).symm g) = g :=
  ⟨(RingedSpaces.Modules.tensorPresheafHomEquiv A B theta M N).symm_apply_apply t,
    (RingedSpaces.Modules.tensorPresheafHomEquiv A B theta M N).apply_symm_apply g⟩

theorem homNaturalityLeft {M M' : RingedSpaces.Modules.Presheaves A}
    (h : M ⟶ M') (N : RingedSpaces.Modules.Presheaves B)
    (t : RingedSpaces.Modules.tensorPresheaf A B theta M' ⟶ N) :
    RingedSpaces.Modules.tensorPresheafHomDown A B theta M
        ((RingedSpaces.Modules.tensorPresheafFunctor A B theta).map h ≫ t) =
      h ≫ RingedSpaces.Modules.tensorPresheafHomDown A B theta M' t := by
  exact RingedSpaces.Modules.tensorPresheafHomDown_naturality_left A B theta h t

theorem homNaturalityRight (M : RingedSpaces.Modules.Presheaves A)
    {N N' : RingedSpaces.Modules.Presheaves B}
    (t : RingedSpaces.Modules.tensorPresheaf A B theta M ⟶ N) (k : N ⟶ N') :
    RingedSpaces.Modules.tensorPresheafHomDown A B theta M (t ≫ k) =
      RingedSpaces.Modules.tensorPresheafHomDown A B theta M t ≫
        (PresheafOfModules.restrictScalars
          (RingedSpaces.Modules.ringMap A B theta)).map k := by
  exact RingedSpaces.Modules.tensorPresheafHomDown_naturality_right A B theta M t k

theorem adjunctionUnitOnSections (M : RingedSpaces.Modules.Presheaves A)
    (U : Cᵒᵖ) (m : M.obj U) :
    ((RingedSpaces.Modules.tensorPresheafAdjunction A B theta).unit.app M).app U m =
      RingedSpaces.Modules.tensorUnitSection A B theta M U m := by
  exact RingedSpaces.Modules.tensorPresheafAdjunction_unit A B theta M U m

theorem adjunctionCounitOnScalars (N : RingedSpaces.Modules.Presheaves B)
    (U : Cᵒᵖ) (b : B.obj U) (n : N.obj U) :
    ((RingedSpaces.Modules.tensorPresheafAdjunction A B theta).counit.app N).app U
        (b • RingedSpaces.Modules.tensorUnitSection A B theta
          ((PresheafOfModules.restrictScalars
            (RingedSpaces.Modules.ringMap A B theta)).obj N) U n) =
      b • n := by
  exact RingedSpaces.Modules.tensorPresheafAdjunction_counit A B theta N U b n

end Test.ModuleChangeOfRings

namespace Test.ModuleChangeOfRings

private def twoObjectArrow :
    Opposite.op (1 : Fin 2) ⟶ Opposite.op (0 : Fin 2) :=
  (homOfLE (by decide : (0 : Fin 2) ≤ 1)).op

private theorem actualTwoObjectArrow (A B : (Fin 2)ᵒᵖ ⥤ CommRingCat.{u}) (theta : A ⟶ B)
    (M : RingedSpaces.Modules.Presheaves A)
    (b : B.obj (Opposite.op (1 : Fin 2))) (m : M.obj (Opposite.op (1 : Fin 2))) :
    (RingedSpaces.Modules.tensorPresheaf A B theta M).map twoObjectArrow
        (b • RingedSpaces.Modules.tensorUnitSection A B theta M (Opposite.op 1) m) =
      B.map twoObjectArrow b •
        RingedSpaces.Modules.tensorUnitSection A B theta M (Opposite.op 0)
          (M.map twoObjectArrow m) := by
  exact RingedSpaces.Modules.tensorRestriction_smul A B theta M twoObjectArrow b m

/-- A literal zero coefficient ring presheaf, without a nontriviality hypothesis. -/
noncomputable def zeroRingPresheaf : (Fin 2)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const (Fin 2)ᵒᵖ).obj (CommRingCat.of PUnit.{u+1})

private theorem zeroRingArrow (M : RingedSpaces.Modules.Presheaves (zeroRingPresheaf.{u}))
    (m : M.obj (Opposite.op (1 : Fin 2))) :
    (RingedSpaces.Modules.tensorPresheaf (zeroRingPresheaf.{u}) (zeroRingPresheaf.{u})
      (𝟙 (zeroRingPresheaf.{u})) M).map twoObjectArrow
        (0 • RingedSpaces.Modules.tensorUnitSection _ _ (𝟙 _) M (Opposite.op 1) m) =
      (zeroRingPresheaf.{u}).map twoObjectArrow 0 •
        RingedSpaces.Modules.tensorUnitSection _ _ (𝟙 _) M (Opposite.op 0)
          (M.map twoObjectArrow m) := by
  exact RingedSpaces.Modules.tensorRestriction_smul _ _ _ M twoObjectArrow 0 m

/-- The presheaf adjunction also exists when the indexing category is empty. -/
noncomputable def emptySiteAdjunction
    (A : (Discrete (PEmpty.{u+1}))ᵒᵖ ⥤ CommRingCat.{u}) :
    RingedSpaces.Modules.tensorPresheafFunctor A A (𝟙 A) ⊣
      PresheafOfModules.restrictScalars (RingedSpaces.Modules.ringMap A A (𝟙 A)) :=
  RingedSpaces.Modules.tensorPresheafAdjunction A A (𝟙 A)

end Test.ModuleChangeOfRings

namespace Test.ModuleChangeOfRings

variable {X : TopCat.{u}} (A B : TopCat.Sheaf CommRingCat.{u} X) (theta : A ⟶ B)

/-- Topological sites infer both sheafification witnesses without hypotheses. -/
noncomputable def topologicalAdjunction :
    RingedSpaces.Modules.tensorSheafFunctor A B theta ⊣
      SheafOfModules.restrictScalars (RingedSpaces.Modules.ringSheafMap A B theta) :=
  RingedSpaces.Modules.opensTensorSheafAdjunction A B theta

theorem sheafUnitGenerator
    (M : RingedSpaces.Modules.Sheaves (J := Opens.grothendieckTopology X) A)
    (U : (Opens X)ᵒᵖ) (m : M.val.obj U) :
    ((RingedSpaces.Modules.tensorSheafAdjunction A B theta).unit.app M).val.app U m =
      (PresheafOfModules.Hom.app
        ((RingedSpaces.Modules.moduleSheafificationAdjunction B).unit.app
          (RingedSpaces.Modules.tensorPresheaf A.obj B.obj theta.hom M.val)) U)
        (RingedSpaces.Modules.tensorUnitSection A.obj B.obj theta.hom M.val U m) := by
  exact RingedSpaces.Modules.tensorSheafAdjunction_unit A B theta M U m

set_option backward.isDefEq.respectTransparency false in
theorem sheafCounitGenerator (N : RingedSpaces.Modules.Sheaves
    (J := Opens.grothendieckTopology X) B)
    (U : (Opens X)ᵒᵖ) (b : B.obj.obj U) (n : N.val.obj U) :
    ((RingedSpaces.Modules.tensorSheafAdjunction A B theta).counit.app N).val.app U
        ((PresheafOfModules.Hom.app
          ((RingedSpaces.Modules.moduleSheafificationAdjunction B).unit.app
            (RingedSpaces.Modules.tensorPresheaf A.obj B.obj theta.hom
              ((SheafOfModules.restrictScalars
                (RingedSpaces.Modules.ringSheafMap A B theta)).obj N).val)) U)
          (b • RingedSpaces.Modules.tensorUnitSection A.obj B.obj theta.hom
            ((SheafOfModules.restrictScalars
              (RingedSpaces.Modules.ringSheafMap A B theta)).obj N).val U n)) =
      b • n := by
  exact RingedSpaces.Modules.tensorSheafAdjunction_counit A B theta N U b n

theorem sheafHomInverses (M : RingedSpaces.Modules.Sheaves
    (J := Opens.grothendieckTopology X) A)
    (N : RingedSpaces.Modules.Sheaves (J := Opens.grothendieckTopology X) B)
    (t : (RingedSpaces.Modules.tensorSheafFunctor A B theta).obj M ⟶ N)
    (g : M ⟶ (SheafOfModules.restrictScalars
      (RingedSpaces.Modules.ringSheafMap A B theta)).obj N) :
    (RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N).symm
        ((RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N) t) = t ∧
      (RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N)
        ((RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N).symm g) = g :=
  ⟨(RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N).symm_apply_apply t,
    (RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N).apply_symm_apply g⟩

theorem sheafHomOnGenerator (M : RingedSpaces.Modules.Sheaves
    (J := Opens.grothendieckTopology X) A)
    (N : RingedSpaces.Modules.Sheaves (J := Opens.grothendieckTopology X) B)
    (t : (RingedSpaces.Modules.tensorSheafFunctor A B theta).obj M ⟶ N)
    (U : (Opens X)ᵒᵖ) (m : M.val.obj U) :
    (RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N t).val.app U m =
      t.val.app U
        ((PresheafOfModules.Hom.app
          ((RingedSpaces.Modules.moduleSheafificationAdjunction B).unit.app
            (RingedSpaces.Modules.tensorPresheaf A.obj B.obj theta.hom M.val)) U)
          (RingedSpaces.Modules.tensorUnitSection A.obj B.obj theta.hom M.val U m)) := by
  exact RingedSpaces.Modules.tensorSheafHomEquiv_apply A B theta M N t U m

theorem sheafHomNaturalityLeft
    {M M' : RingedSpaces.Modules.Sheaves (J := Opens.grothendieckTopology X) A}
    (h : M ⟶ M') (N : RingedSpaces.Modules.Sheaves (J := Opens.grothendieckTopology X) B)
    (t : (RingedSpaces.Modules.tensorSheafFunctor A B theta).obj M' ⟶ N) :
    RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N
        ((RingedSpaces.Modules.tensorSheafFunctor A B theta).map h ≫ t) =
      h ≫ RingedSpaces.Modules.tensorSheafHomEquiv A B theta M' N t := by
  exact RingedSpaces.Modules.tensorSheafHomEquiv_naturality_left A B theta h N t

theorem sheafHomNaturalityRight
    (M : RingedSpaces.Modules.Sheaves (J := Opens.grothendieckTopology X) A)
    {N N' : RingedSpaces.Modules.Sheaves (J := Opens.grothendieckTopology X) B}
    (t : (RingedSpaces.Modules.tensorSheafFunctor A B theta).obj M ⟶ N)
    (k : N ⟶ N') :
    RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N' (t ≫ k) =
      RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N t ≫
        (SheafOfModules.restrictScalars
          (RingedSpaces.Modules.ringSheafMap A B theta)).map k := by
  exact RingedSpaces.Modules.tensorSheafHomEquiv_naturality_right A B theta M t k

theorem sheafAdjunctionUnitNaturality
    {M M' : RingedSpaces.Modules.Sheaves (J := Opens.grothendieckTopology X) A}
    (h : M ⟶ M') :
    (RingedSpaces.Modules.tensorSheafAdjunction A B theta).unit.app M ≫
        (SheafOfModules.restrictScalars
          (RingedSpaces.Modules.ringSheafMap A B theta)).map
          ((RingedSpaces.Modules.tensorSheafFunctor A B theta).map h) =
      h ≫ (RingedSpaces.Modules.tensorSheafAdjunction A B theta).unit.app M' :=
  (RingedSpaces.Modules.tensorSheafAdjunction A B theta).unit_naturality h

theorem sheafAdjunctionCounitNaturality
    {N N' : RingedSpaces.Modules.Sheaves (J := Opens.grothendieckTopology X) B}
    (k : N ⟶ N') :
    (RingedSpaces.Modules.tensorSheafFunctor A B theta).map
        ((SheafOfModules.restrictScalars
          (RingedSpaces.Modules.ringSheafMap A B theta)).map k) ≫
        (RingedSpaces.Modules.tensorSheafAdjunction A B theta).counit.app N' =
      (RingedSpaces.Modules.tensorSheafAdjunction A B theta).counit.app N ≫ k :=
  by
    simpa only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] using
      (RingedSpaces.Modules.tensorSheafAdjunction A B theta).counit.naturality k

/-- The topological adjunction does not require points in the underlying space. -/
noncomputable def emptySpaceAdjunction
    (A B : TopCat.Sheaf CommRingCat.{u} (TopCat.of (PEmpty.{u+1}))) (theta : A ⟶ B) :
    RingedSpaces.Modules.tensorSheafFunctor A B theta ⊣
      SheafOfModules.restrictScalars (RingedSpaces.Modules.ringSheafMap A B theta) :=
  RingedSpaces.Modules.opensTensorSheafAdjunction A B theta

end Test.ModuleChangeOfRings
