/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Test.PresheafInverseImage
public import Mathlib.Data.ZMod.Defs

/-!
# Concrete and boundary inverse-image clients

The constant integer module on a two-point discrete space tests a nonidentity
base map and a restriction to a nonempty proper open. Constant presheaves need
not satisfy a sheaf condition, even over the empty open.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open RingedSpaces.Modules.PresheafInverseImage

namespace Test.PresheafInverseImageConcrete

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
  PresheafOfModules.ofPresheaf
    ((Functor.const _).obj (AddCommGrpCat.of ℤ))
    (fun {_ _} _ _ _ => rfl)

private def singletonOpen : Opens (TopCat.of (Fin 2)) :=
  ⟨{(0 : Fin 2)}, isOpen_discrete _⟩

private def properRestriction : op (⊤ : Opens (TopCat.of (Fin 2))) ⟶
    op (⟨{(0 : Fin 2)}, isOpen_discrete _⟩ : Opens (TopCat.of (Fin 2))) :=
  (homOfLE (le_top : singletonOpen ≤ (⊤ : Opens twoPoints))).op

theorem genuinelyProperNonempty :
    singletonOpen ≠ (⊤ : Opens twoPoints) ∧ (0 : Fin 2) ∈ singletonOpen := by
  constructor
  · intro h
    have atOne := congrArg (fun U : Opens twoPoints => (1 : Fin 2) ∈ U) h
    simp [singletonOpen] at atOne
  · simp [singletonOpen]

theorem nonidentityNonzeroInputs :
    collapse ≠ 𝟙 twoPoints ∧ (2 : integers.obj (op (⊤ : Opens twoPoints))) ≠ 0 ∧
      (show integerModule.obj (op (⊤ : Opens twoPoints)) from (3 : ℤ)) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro equality
    have atOne := congrArg (fun g : twoPoints ⟶ twoPoints => g (1 : twoPoints)) equality
    change (0 : Fin 2) = 1 at atOne
    exact (by decide : (0 : Fin 2) ≠ 1) atOne
  · change (2 : ℤ) ≠ 0
    decide
  · change (3 : ℤ) ≠ 0
    decide

theorem nonidentityGenerator (V : (Opens twoPoints)ᵒᵖ)
    (r : integers.obj V) (m : integerModule.obj V) :
    pointwiseSmul collapse integers integerModule ((Opens.map collapse).obj (unop V))
        (((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integers).app V r)
        (((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integerModule.presheaf).app V m) =
      ((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integerModule.presheaf).app V
        (r • m) :=
  unit_smul collapse integers integerModule V r m

theorem nonzeroInputGenerator :
    pointwiseSmul collapse integers integerModule (⊤ : Opens twoPoints)
        (((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integers).app
          (op (⊤ : Opens twoPoints)) (2 : ℤ))
        (((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integerModule.presheaf).app
          (op (⊤ : Opens twoPoints))
          (show integerModule.obj (op (⊤ : Opens twoPoints)) from (3 : ℤ))) =
      ((Opens.map collapse).op.pointwiseLeftKanExtensionUnit integerModule.presheaf).app
        (op (⊤ : Opens twoPoints))
        ((2 : ℤ) • (show integerModule.obj (op (⊤ : Opens twoPoints)) from (3 : ℤ))) := by
  exact nonidentityGenerator (op (⊤ : Opens twoPoints)) (2 : ℤ)
    (show integerModule.obj (op (⊤ : Opens twoPoints)) from (3 : ℤ))

theorem properOpenArbitraryScalar
    (r : ((Opens.map collapse).op.pointwiseLeftKanExtension integers).obj
      (op (⊤ : Opens twoPoints)))
    (m : ((Opens.map collapse).op.pointwiseLeftKanExtension integerModule.presheaf).obj
      (op (⊤ : Opens twoPoints))) :
    letI := pointwiseModule collapse integers integerModule (⊤ : Opens twoPoints)
    letI := pointwiseModule collapse integers integerModule singletonOpen
    (inverseImageModule collapse integers integerModule).map properRestriction (r • m) =
      ((Opens.map collapse).op.pointwiseLeftKanExtension integers).map properRestriction r •
        (inverseImageModule collapse integers integerModule).map properRestriction m :=
  restriction_smul collapse integers integerModule properRestriction r m

private abbrev emptySpace : TopCat := @TopCat.of PEmpty ⊤

private def fromEmpty : emptySpace ⟶ twoPoints := TopCat.const (0 : twoPoints)

theorem emptySourceUnit (V : (Opens twoPoints)ᵒᵖ)
    (r : integers.obj V) (m : integerModule.obj V) :
    pointwiseSmul fromEmpty integers integerModule ((Opens.map fromEmpty).obj (unop V))
        (((Opens.map fromEmpty).op.pointwiseLeftKanExtensionUnit integers).app V r)
        (((Opens.map fromEmpty).op.pointwiseLeftKanExtensionUnit integerModule.presheaf).app V m) =
      ((Opens.map fromEmpty).op.pointwiseLeftKanExtensionUnit integerModule.presheaf).app V
        (r • m) :=
  unit_smul fromEmpty integers integerModule V r m

theorem emptyOpenRestriction
    (r : ((Opens.map collapse).op.pointwiseLeftKanExtension integers).obj
      (op (⊤ : Opens twoPoints)))
    (m : ((Opens.map collapse).op.pointwiseLeftKanExtension integerModule.presheaf).obj
      (op (⊤ : Opens twoPoints))) :
    letI := pointwiseModule collapse integers integerModule (⊤ : Opens twoPoints)
    letI := pointwiseModule collapse integers integerModule (⊥ : Opens twoPoints)
    (inverseImageModule collapse integers integerModule).map
        ((homOfLE (bot_le : (⊥ : Opens twoPoints) ≤ ⊤)).op) (r • m) =
      ((Opens.map collapse).op.pointwiseLeftKanExtension integers).map
          ((homOfLE (bot_le : (⊥ : Opens twoPoints) ≤ ⊤)).op) r •
        (inverseImageModule collapse integers integerModule).map
          ((homOfLE (bot_le : (⊥ : Opens twoPoints) ≤ ⊤)).op) m :=
  restriction_smul collapse integers integerModule _ r m

private abbrev zeroRing : (TopCat.of (Fin 2)).Presheaf RingCat :=
  (Functor.const _).obj (RingCat.of (ZMod 1))

private instance (U : (Opens (TopCat.of (Fin 2)))ᵒᵖ) :
    Module (((Functor.const _).obj (RingCat.of (ZMod 1))).obj U)
      (((Functor.const _).obj (AddCommGrpCat.of (ZMod 1))).obj U) := by
  change Module (ZMod 1) (ZMod 1)
  infer_instance

private noncomputable def zeroModule : PresheafOfModules.{0} zeroRing :=
  PresheafOfModules.ofPresheaf
    ((Functor.const _).obj (AddCommGrpCat.of (ZMod 1)))
    (fun {_ _} _ _ _ => rfl)

theorem zeroRingIsTrivial (V : (Opens twoPoints)ᵒᵖ) :
    (0 : zeroRing.obj V) = 1 := by
  change (0 : ZMod 1) = 1
  exact Subsingleton.elim _ _

theorem zeroRingAction (V : (Opens twoPoints)ᵒᵖ)
    (r : zeroRing.obj V) (m : zeroModule.obj V) :
    pointwiseSmul collapse zeroRing zeroModule ((Opens.map collapse).obj (unop V))
        (((Opens.map collapse).op.pointwiseLeftKanExtensionUnit zeroRing).app V r)
        (((Opens.map collapse).op.pointwiseLeftKanExtensionUnit zeroModule.presheaf).app V m) =
      ((Opens.map collapse).op.pointwiseLeftKanExtensionUnit zeroModule.presheaf).app V
        (r • m) :=
  unit_smul collapse zeroRing zeroModule V r m

end Test.PresheafInverseImageConcrete
