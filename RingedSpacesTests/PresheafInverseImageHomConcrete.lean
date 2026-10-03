/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpacesTests.PresheafInverseImageHom
public import Mathlib.Data.ZMod.Defs

/-!
# Geometric and boundary clients for inverse-image Hom

A constant integer presheaf over the two-point discrete space supplies a
nonidentity collapse map and a nonempty proper open. No nonzero statement about
its Kan colimits is inferred from the nonzero input sections.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open RingedSpaces.Modules.PresheafInverseImage

namespace Test.PresheafInverseImageHomConcrete

private local instance : TopologicalSpace (Fin 2) := ⊥
private local instance : DiscreteTopology (Fin 2) := discreteTopology_bot (Fin 2)

private abbrev twoPoints : TopCat := TopCat.of (Fin 2)
private def collapse : twoPoints ⟶ twoPoints := TopCat.const (0 : twoPoints)
private abbrev integers : (TopCat.of (Fin 2)).Presheaf RingCat :=
  (Functor.const _).obj (RingCat.of ℤ)

private instance (U : (Opens (TopCat.of (Fin 2)))ᵒᵖ) :
    Module (((Functor.const _).obj (RingCat.of ℤ)).obj U)
      (((Functor.const _).obj (AddCommGrpCat.of ℤ)).obj U) := by
  change Module ℤ ℤ
  infer_instance

private noncomputable abbrev integerModule : PresheafOfModules.{0} integers :=
  PresheafOfModules.ofPresheaf ((Functor.const _).obj (AddCommGrpCat.of ℤ))
    (fun {_ _} _ _ _ => rfl)

private noncomputable abbrev pulledModule :
    PresheafOfModules.{0} ((Opens.map collapse).op.pointwiseLeftKanExtension integers) :=
  (inverseImageFunctor collapse integers).obj integerModule

private def singletonOpen : Opens (TopCat.of (Fin 2)) :=
  ⟨{(0 : Fin 2)}, isOpen_discrete _⟩

private def properRestriction : op (⊤ : Opens (TopCat.of (Fin 2))) ⟶
    op (⟨{(0 : Fin 2)}, isOpen_discrete _⟩ : Opens (TopCat.of (Fin 2))) :=
  (homOfLE (le_top : singletonOpen ≤ (⊤ : Opens twoPoints))).op

theorem genuinelyProperOpenAndNonidentity :
    singletonOpen ≠ (⊤ : Opens twoPoints) ∧
      (0 : Fin 2) ∈ singletonOpen ∧ collapse ≠ 𝟙 twoPoints := by
  refine ⟨?_, ?_, ?_⟩
  · intro equality
    have atOne := congrArg (fun U : Opens twoPoints => (1 : Fin 2) ∈ U) equality
    simp [singletonOpen] at atOne
  · simp [singletonOpen]
  · intro equality
    have atOne := congrArg (fun g : twoPoints ⟶ twoPoints => g (1 : twoPoints)) equality
    change (0 : Fin 2) = 1 at atOne
    exact (by decide : (0 : Fin 2) ≠ 1) atOne

theorem nonzeroInputSections :
    (2 : integers.obj (op (⊤ : Opens twoPoints))) ≠ 0 ∧
      (show integerModule.obj (op (⊤ : Opens twoPoints)) from (3 : ℤ)) ≠ 0 := by
  constructor
  · change (2 : ℤ) ≠ 0
    decide
  · change (3 : ℤ) ≠ 0
    decide

theorem concreteBothDirections :
    (homEquiv collapse integers integerModule pulledModule).symm
      ((homEquiv collapse integers integerModule pulledModule) (𝟙 pulledModule)) =
        𝟙 pulledModule ∧
    (homEquiv collapse integers integerModule pulledModule)
      ((homEquiv collapse integers integerModule pulledModule).symm
        (forward collapse integers (𝟙 pulledModule))) =
        forward collapse integers (𝟙 pulledModule) :=
  Test.PresheafInverseImageHom.bothHomDirections collapse integers integerModule
    pulledModule (𝟙 pulledModule) (forward collapse integers (𝟙 pulledModule))

theorem concreteNonzeroForwardSection :
    (forward collapse integers (𝟙 pulledModule)).app (op (⊤ : Opens twoPoints))
      (show integerModule.obj (op (⊤ : Opens twoPoints)) from (3 : ℤ)) =
      (((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integerModule.presheaf).app
        (op (⊤ : Opens twoPoints))
        (show integerModule.obj (op (⊤ : Opens twoPoints)) from (3 : ℤ))) := by
  rw [forward_apply collapse integers (𝟙 pulledModule)]
  rfl

theorem properOpenArbitraryCoefficient
    (r : ((Opens.map collapse).op.pointwiseLeftKanExtension integers).obj
      (op singletonOpen)) (m : pulledModule.obj (op singletonOpen)) :
    (backward collapse integers
      (forward collapse integers (𝟙 pulledModule))).app (op singletonOpen) (r • m) =
      r • (backward collapse integers
        (forward collapse integers (𝟙 pulledModule))).app (op singletonOpen) m :=
  backward_smul collapse integers _ _ r m

theorem properOpenRestrictionNaturality
    (m : pulledModule.obj (op (⊤ : Opens twoPoints))) :
    pulledModule.map properRestriction
        ((backward collapse integers
          (forward collapse integers (𝟙 pulledModule))).app (op (⊤ : Opens twoPoints)) m) =
      (backward collapse integers
        (forward collapse integers (𝟙 pulledModule))).app (op singletonOpen)
          (pulledModule.map properRestriction m) := by
  exact (PresheafOfModules.naturality_apply
    (backward collapse integers (forward collapse integers (𝟙 pulledModule)))
    properRestriction m).symm

theorem properOpenCounit (i : index collapse singletonOpen)
    (m : ((PresheafOfModules.pushforward (F := Opens.map collapse)
      ((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integers)).obj
        pulledModule).obj i.left) :
    ((adjunction collapse integers).counit.app pulledModule).app (op singletonOpen)
      ((colimit.ι (CostructuredArrow.proj (Opens.map collapse).op (op singletonOpen) ⋙
        ((PresheafOfModules.pushforward (F := Opens.map collapse)
          ((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integers)).obj
            pulledModule).presheaf) i) m) =
      pulledModule.map i.hom m :=
  counit_ι collapse integers pulledModule singletonOpen i m

theorem nonzeroUnitSection :
    ((adjunction collapse integers).unit.app integerModule).app
      (op (⊤ : Opens twoPoints))
      (show integerModule.obj (op (⊤ : Opens twoPoints)) from (3 : ℤ)) =
      ((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integerModule.presheaf).app
        (op (⊤ : Opens twoPoints))
        (show integerModule.obj (op (⊤ : Opens twoPoints)) from (3 : ℤ)) :=
  unit_apply collapse integers integerModule _ _

theorem concreteMapsAndTriangles :
    forward collapse integers
        ((inverseImageFunctor collapse integers).map (𝟙 integerModule) ≫
          (𝟙 pulledModule)) =
      (𝟙 integerModule) ≫ forward collapse integers (𝟙 pulledModule) ∧
    (inverseImageFunctor collapse integers).map
        ((adjunction collapse integers).unit.app integerModule) ≫
      (adjunction collapse integers).counit.app pulledModule = 𝟙 _ ∧
    forward collapse integers ((𝟙 pulledModule) ≫ (𝟙 pulledModule)) =
      forward collapse integers (𝟙 pulledModule) ≫
        (PresheafOfModules.pushforward (F := Opens.map collapse)
          ((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integers)).map
            (𝟙 pulledModule) := by
  refine ⟨forward_naturality_left collapse integers (𝟙 integerModule)
    (𝟙 pulledModule), (adjunction collapse integers).left_triangle_components _, ?_⟩
  exact forward_naturality_right collapse integers (𝟙 pulledModule) (𝟙 pulledModule)

theorem concreteRightTriangle :
    (adjunction collapse integers).unit.app
        ((PresheafOfModules.pushforward (F := Opens.map collapse)
          ((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integers)).obj
            pulledModule) ≫
      (PresheafOfModules.pushforward (F := Opens.map collapse)
        ((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integers)).map
          ((adjunction collapse integers).counit.app pulledModule) = 𝟙 _ :=
  (adjunction collapse integers).right_triangle_components _

theorem concreteAdditiveTranspose :
    (PresheafOfModules.toPresheaf integers).map
        (forward collapse integers (𝟙 pulledModule)) ≫
      ((PresheafOfModules.pushforwardCompToPresheaf (F := Opens.map collapse)
        ((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integers)).app
          pulledModule).hom =
      (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} collapse).homEquiv
        integerModule.presheaf pulledModule.presheaf
          ((underlyingComparison collapse integers).inv.app integerModule ≫
            (PresheafOfModules.toPresheaf _).map (𝟙 pulledModule)) :=
  forward_underlying_additive collapse integers (𝟙 pulledModule)

private abbrev emptySpace : TopCat := @TopCat.of PEmpty ⊤
private def fromEmpty : emptySpace ⟶ twoPoints := TopCat.const (0 : twoPoints)

noncomputable def emptySourceHomEquiv :
    ((inverseImageFunctor fromEmpty integers).obj integerModule ⟶
      (inverseImageFunctor fromEmpty integers).obj integerModule) ≃
      (integerModule ⟶ (PresheafOfModules.pushforward (F := Opens.map fromEmpty)
        ((Opens.map fromEmpty).op.pointwiseLeftKanExtensionUnit integers)).obj
          ((inverseImageFunctor fromEmpty integers).obj integerModule)) :=
  homEquiv fromEmpty integers _ _

private abbrev zeroRing : (TopCat.of (Fin 2)).Presheaf RingCat :=
  (Functor.const _).obj (RingCat.of (ZMod 1))

private instance (U : (Opens (TopCat.of (Fin 2)))ᵒᵖ) :
    Module (((Functor.const _).obj (RingCat.of (ZMod 1))).obj U)
      (((Functor.const _).obj (AddCommGrpCat.of (ZMod 1))).obj U) := by
  change Module (ZMod 1) (ZMod 1)
  infer_instance

private noncomputable abbrev zeroModule : PresheafOfModules.{0} zeroRing :=
  PresheafOfModules.ofPresheaf
    ((Functor.const _).obj (AddCommGrpCat.of (ZMod 1)))
    (fun {_ _} _ _ _ => rfl)

noncomputable def zeroRingHomEquiv :
    ((inverseImageFunctor collapse zeroRing).obj zeroModule ⟶
      (inverseImageFunctor collapse zeroRing).obj zeroModule) ≃
      (zeroModule ⟶ (PresheafOfModules.pushforward (F := Opens.map collapse)
        ((Opens.map collapse).op.pointwiseLeftKanExtensionUnit zeroRing)).obj
          ((inverseImageFunctor collapse zeroRing).obj zeroModule)) :=
  homEquiv collapse zeroRing _ _

end Test.PresheafInverseImageHomConcrete
