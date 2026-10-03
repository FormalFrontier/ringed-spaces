/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.PresheafChangeOfRingsSymmetry
public import RingedSpaces.Modules.SheafChangeOfRingsSymmetry
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Direct-import consumers of right-factor change of rings

The coefficient map and site are arbitrary in the main clients. The nonidentity
arrow, zero ring, empty site and topological boundary clients exercise the same API.
-/

@[expose] public section

open CategoryTheory TopologicalSpace RingedSpaces.Modules

universe u v₁ u₁

namespace Test.ChangeOfRingsSymmetry

variable {C : Type u₁} [Category.{v₁} C]
  (A B : Cᵒᵖ ⥤ CommRingCat.{u}) (theta : A ⟶ B)
  (M : Presheaves A) (U : Cᵒᵖ)

theorem arbitraryCoefficients (m : M.obj U) (b c : B.obj U) :
    rightSectionSmul A B theta M U c (rightPure A B theta M U m b) =
      rightPure A B theta M U m (c * b) :=
  smul_pure A B theta M U m b c

theorem balanceForFullMap (a : A.obj U) (m : M.obj U) (b : B.obj U) :
    rightPure A B theta M U ((M.obj U).isModule.smul a m) b =
      rightPure A B theta M U m ((theta.app U).hom a * b) :=
  rightBalance_pure A B theta M U a m b

theorem arbitraryTensorCompatibility (a : A.obj U)
    (t : rightSectionCat A B theta M U) :
    (rightSection A B theta M U).isModule.smul a t =
      rightSectionSmul A B theta M U ((theta.app U).hom a) t :=
  theta_smul A B theta M U a t

theorem comparisonBothDirections (m : M.obj U) (b : B.obj U) :
    (rightSectionIso A B theta M U).hom (rightPure A B theta M U m b) =
      leftPure A B theta M U b m ∧
    (rightSectionIso A B theta M U).inv (leftPure A B theta M U b m) =
      rightPure A B theta M U m b :=
  ⟨rightSectionIso_pure A B theta M U m b,
    rightSectionIso_inv_tmul A B theta M U m b⟩

theorem actualArrowRestriction {V : Cᵒᵖ} (f : U ⟶ V)
    (m : M.obj U) (b c : B.obj U) (t : rightSectionCat A B theta M U) :
    (rightPresheaf A B theta M).map f (rightPure A B theta M U m b) =
        rightPure A B theta M V (M.map f m) (B.map f b) ∧
      rightRestriction A B theta M f (rightSectionSmul A B theta M U c t) =
        rightSectionSmul A B theta M V (B.map f c)
          (rightRestriction A B theta M f t) :=
  ⟨rightRestriction_pure A B theta M f m b,
    rightRestriction_semilinear A B theta M f c t⟩

theorem arbitraryMorphismNaturality {N : Presheaves A} (h : M ⟶ N)
    {V : Cᵒᵖ} (f : U ⟶ V) (m : M.obj U) (b : B.obj U)
    (t : rightSectionCat A B theta M U) :
    ((rightPresheafFunctor A B theta).map h).app U
        (rightPure A B theta M U m b) =
        rightPure A B theta N U (h.app U m) b ∧
      rightRestriction A B theta N f (rightSectionMap A B theta h U t) =
        rightSectionMap A B theta h V (rightRestriction A B theta M f t) :=
  ⟨rightPresheafMap_pure A B theta h U m b,
    rightPresheafMap_restriction A B theta h f t⟩

theorem rightFunctorLaws {N P : Presheaves A} (h : M ⟶ N) (k : N ⟶ P)
    {V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (t : rightSectionCat A B theta M U) :
    (rightPresheaf A B theta M).map (f ≫ g) t =
        (rightPresheaf A B theta M).map g
          ((rightPresheaf A B theta M).map f t) ∧
      (rightPresheafFunctor A B theta).map (𝟙 M) = 𝟙 _ ∧
      (rightPresheafFunctor A B theta).map (h ≫ k) =
        (rightPresheafFunctor A B theta).map h ≫
          (rightPresheafFunctor A B theta).map k :=
  ⟨(rightPresheaf A B theta M).map_comp_apply f g t,
    (rightPresheafFunctor A B theta).map_id M,
    (rightPresheafFunctor A B theta).map_comp h k⟩

theorem rightIdentityOnPure (m : M.obj U) (b : B.obj U) :
    (rightPresheaf A B theta M).map (𝟙 U) (rightPure A B theta M U m b) =
      rightPure A B theta M U m b := by
  change rightRestriction A B theta M (𝟙 U) (rightPure A B theta M U m b) = _
  rw [rightRestriction_pure]
  simp
  rfl

theorem unitAndComparison (m : M.obj U) :
    (rightPresheafUnit A B theta M).app U m = rightPure A B theta M U m 1 ∧
      (rightPresheafIso A B theta M).hom.app U
        ((rightPresheafUnit A B theta M).app U m) =
          (presheafTensorUnit A B theta M).app U m := by
  constructor
  · exact rightPresheafUnit_pure A B theta M U m
  · rw [rightPresheafUnit_pure]
    change (rightSectionIso A B theta M U).hom (rightPure A B theta M U m 1) =
      tensorUnitSection A B theta M U m
    rw [rightSectionIso_pure]
    exact (unit_eq_leftPure A B theta M U m).symm

set_option backward.isDefEq.respectTransparency false in
theorem homFormulaViaComparison {N : Presheaves B}
    (g : M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj N)
    (m : M.obj U) (b : B.obj U) :
    letI : Module (B.obj U)
      (((PresheafOfModules.restrictScalars (ringMap A B theta)).obj N).obj U) :=
        (N.obj U).isModule
    ((rightPresheafIso A B theta M).hom ≫ tensorPresheafHomUp A B theta M g).app U
      (rightPure A B theta M U m b) = b • g.app U m := by
  change (tensorPresheafHomUp A B theta M g).app U
    ((rightSectionIso A B theta M U).hom (rightPure A B theta M U m b)) = _
  rw [rightSectionIso_pure, leftPure_eq_smul_unit]
  exact tensorPresheafHomUp_smul A B theta M g U b m

private def actualArrow :
    Opposite.op (1 : Fin 2) ⟶ Opposite.op (0 : Fin 2) :=
  (homOfLE (by decide : (0 : Fin 2) ≤ 1)).op

private theorem twoObjectArrowClient (A B : (Fin 2)ᵒᵖ ⥤ CommRingCat.{u}) (theta : A ⟶ B)
    (M : Presheaves A) (m : M.obj (Opposite.op (1 : Fin 2)))
    (b c : B.obj (Opposite.op (1 : Fin 2))) :
    (rightPresheaf A B theta M).map actualArrow
        (rightSectionSmul A B theta M (Opposite.op 1) c
          (rightPure A B theta M (Opposite.op 1) m b)) =
      rightSectionSmul A B theta M (Opposite.op 0) (B.map actualArrow c)
        (rightPure A B theta M (Opposite.op 0) (M.map actualArrow m)
          (B.map actualArrow b)) := by
  change rightRestriction A B theta M actualArrow
      (rightSectionSmul A B theta M (Opposite.op 1) c
        (rightPure A B theta M (Opposite.op 1) m b)) = _
  rw [rightRestriction_semilinear, rightRestriction_pure]

/-- The tensor comparison exists on a site with no objects. -/
noncomputable def emptySiteComparison
    (A : (Discrete (PEmpty.{u+1}))ᵒᵖ ⥤ CommRingCat.{u}) :
    rightPresheafFunctor A A (𝟙 A) ≅ tensorPresheafFunctor A A (𝟙 A) :=
  rightPresheafNatIso A A (𝟙 A)

/-- A constant zero ring, without a nontriviality assumption. -/
noncomputable def zeroRingPresheaf : (Fin 2)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const (Fin 2)ᵒᵖ).obj (CommRingCat.of PUnit.{u+1})

/-- Tensor comparison also exists for zero coefficient rings. -/
noncomputable def zeroRingArrowComparison :
    rightPresheafFunctor zeroRingPresheaf zeroRingPresheaf (𝟙 zeroRingPresheaf) ≅
      tensorPresheafFunctor zeroRingPresheaf zeroRingPresheaf (𝟙 zeroRingPresheaf) :=
  rightPresheafNatIso _ _ _

end Test.ChangeOfRingsSymmetry

namespace Test.ChangeOfRingsSymmetry

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  (A B : Sheaf J CommRingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (theta : A ⟶ B) (M : Sheaves A)

theorem sheafificationComparisonSquare :
    (rightPresheafIso A.obj B.obj theta.hom M.val).hom ≫
        (moduleSheafificationAdjunction B).unit.app
          (tensorPresheaf A.obj B.obj theta.hom M.val) =
      (moduleSheafificationAdjunction B).unit.app
          (rightPresheaf A.obj B.obj theta.hom M.val) ≫
        (SheafOfModules.forget (ringSheaf B) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf B).obj)).map
          ((rightSheafNatIso A B theta).hom.app M) :=
  rightSheafificationUnit_naturality A B theta M

end Test.ChangeOfRingsSymmetry

#lint-
