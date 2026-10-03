/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces
public import RingedSpacesTests.ChangeOfRingsSymmetryFixture
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Aggregate-import clients of right-factor scalar extension
-/

@[expose] public section

open CategoryTheory TopologicalSpace RingedSpaces.Modules

universe u v₁ u₁

namespace Test.ChangeOfRingsSymmetryRoot

variable {C : Type u₁} [Category.{v₁} C]
  (A B : Cᵒᵖ ⥤ CommRingCat.{u}) (theta : A ⟶ B)
  (M : Presheaves A) (U : Cᵒᵖ)

theorem rootComparisonOnArbitraryCoefficient (m : M.obj U) (b : B.obj U) :
    ((rightPresheafNatIso A B theta).hom.app M).app U
        (rightPure A B theta M U m b) =
      leftPure A B theta M U b m :=
  rightSectionIso_pure A B theta M U m b

theorem rootNonidentityDiagram
    (M : Presheaves Test.ChangeOfRingsSymmetryFixture.constantIntegers)
    (m : M.obj (Opposite.op (1 : Fin 2))) :
    (rightPresheaf Test.ChangeOfRingsSymmetryFixture.constantIntegers
      Test.ChangeOfRingsSymmetryFixture.changingRing
      Test.ChangeOfRingsSymmetryFixture.integerInclusion M).map
        ((homOfLE (by decide : (0 : Fin 2) ≤ 1)).op)
        (rightSectionSmul Test.ChangeOfRingsSymmetryFixture.constantIntegers
          Test.ChangeOfRingsSymmetryFixture.changingRing
          Test.ChangeOfRingsSymmetryFixture.integerInclusion M (Opposite.op 1) 3
          (rightPure Test.ChangeOfRingsSymmetryFixture.constantIntegers
            Test.ChangeOfRingsSymmetryFixture.changingRing
            Test.ChangeOfRingsSymmetryFixture.integerInclusion M (Opposite.op 1) m 2)) =
      rightSectionSmul Test.ChangeOfRingsSymmetryFixture.constantIntegers
        Test.ChangeOfRingsSymmetryFixture.changingRing
        Test.ChangeOfRingsSymmetryFixture.integerInclusion M (Opposite.op 0) (3 : ℚ)
        (rightPure Test.ChangeOfRingsSymmetryFixture.constantIntegers
          Test.ChangeOfRingsSymmetryFixture.changingRing
          Test.ChangeOfRingsSymmetryFixture.integerInclusion M (Opposite.op 0)
          (M.map ((homOfLE (by decide : (0 : Fin 2) ≤ 1)).op) m) (2 : ℚ)) :=
  Test.ChangeOfRingsSymmetryFixture.nontrivialTwoCoefficientRestriction M m

end Test.ChangeOfRingsSymmetryRoot

end

open CategoryTheory TopologicalSpace RingedSpaces.Modules

universe u v₁ u₁

namespace Test.ChangeOfRingsSymmetryRoot

/-- A discrete two-point topology used only inside this test namespace. -/
local instance twoPointDiscreteTopology : TopologicalSpace (Fin 2) := ⊥

private abbrev twoPointSpace := TopCat.of (Fin 2)

theorem emptyOpenIsProper :
    (⊥ : Opens twoPointSpace) ≠ (⊤ : Opens twoPointSpace) := by
  intro h
  have hmem : (0 : Fin 2) ∈ (⊥ : Opens twoPointSpace) := by
    rw [h]
    trivial
  exact hmem

variable (A B : TopCat.Sheaf CommRingCat.{0} twoPointSpace) (theta : A ⟶ B)
  (M : Sheaves (J := Opens.grothendieckTopology twoPointSpace) A)

theorem properOpenRestrictionAndSheafification
    (m : M.val.obj (Opposite.op (⊤ : Opens twoPointSpace)))
    (b : B.obj.obj (Opposite.op (⊤ : Opens twoPointSpace))) :
    (rightPresheaf A.obj B.obj theta.hom M.val).map
      (homOfLE (bot_le : (⊥ : Opens twoPointSpace) ≤ ⊤)).op
        (rightPure A.obj B.obj theta.hom M.val (Opposite.op ⊤) m b) =
      rightPure A.obj B.obj theta.hom M.val (Opposite.op ⊥)
        (M.val.map (homOfLE (bot_le : (⊥ : Opens twoPointSpace) ≤ ⊤)).op m)
        (B.obj.map (homOfLE (bot_le : (⊥ : Opens twoPointSpace) ≤ ⊤)).op b) := by
  exact rightRestriction_pure A.obj B.obj theta.hom M.val _ m b

/-- The topological two-point example discharges the native sheaf witnesses. -/
noncomputable def twoPointSheafComparison :
    rightSheafFunctor A B theta ≅ tensorSheafFunctor A B theta :=
  opensRightSheafNatIso A B theta

end Test.ChangeOfRingsSymmetryRoot

namespace Test.ChangeOfRingsSymmetryRoot

private def selectedOpen : Opens (TopCat.of (Fin 2)) :=
  ⟨{0}, isOpen_discrete _⟩

theorem selectedOpen_nonempty : (selectedOpen : Set (Fin 2)).Nonempty := by
  refine ⟨0, ?_⟩
  simp [selectedOpen]

theorem selectedOpen_proper : selectedOpen ≠ ⊤ := by
  intro h
  have hmem : (1 : Fin 2) ∈ selectedOpen := by
    rw [h]
    trivial
  have hne : (1 : Fin 2) ≠ 0 := by decide
  change (1 : Fin 2) ∈ ({0} : Set (Fin 2)) at hmem
  have : (1 : Fin 2) = 0 := by simpa only [Set.mem_singleton_iff] using hmem
  exact hne this

private theorem selectedOpen_le_top : selectedOpen ≤ ⊤ := le_top

/-- The skyscraper with nonzero integer coefficients at the selected point. -/
noncomputable def integerSkyscraper : TopCat.Sheaf CommRingCat twoPointSpace := by
  classical
  exact skyscraperSheaf (X := twoPointSpace) (0 : Fin 2) (CommRingCat.of ℤ)

/-- The integer skyscraper as a rank-one sheaf of modules over itself. -/
noncomputable def integerModule : Sheaves integerSkyscraper :=
  SheafOfModules.unit (ringSheaf integerSkyscraper)

private noncomputable def selectedInput :
    integerModule.val.obj (Opposite.op (⊤ : Opens twoPointSpace)) := by
  change integerSkyscraper.obj.obj (Opposite.op (⊤ : Opens twoPointSpace))
  exact 1

theorem selectedInput_ne_zero : selectedInput ≠ 0 := by
  have hobj : (ringSheaf integerSkyscraper).obj.obj
      (Opposite.op (⊤ : Opens twoPointSpace)) = RingCat.of ℤ := by
    simp [ringSheaf, integerSkyscraper, skyscraperSheaf, skyscraperPresheaf]
    rfl
  have hne : (1 : (ringSheaf integerSkyscraper).obj.obj
      (Opposite.op (⊤ : Opens twoPointSpace))) ≠ 0 := by
    rw [hobj]
    exact one_ne_zero
  change (1 : (ringSheaf integerSkyscraper).obj.obj
    (Opposite.op (⊤ : Opens twoPointSpace))) ≠ 0
  exact hne

private noncomputable def integerTheta : integerSkyscraper ⟶ integerSkyscraper := 𝟙 _

theorem nonemptyProperOpenComparison :
    (rightPresheafIso integerSkyscraper.obj integerSkyscraper.obj
      integerTheta.hom integerModule.val).hom.app (Opposite.op selectedOpen)
        ((rightPresheaf integerSkyscraper.obj integerSkyscraper.obj
          integerTheta.hom integerModule.val).map
          (homOfLE selectedOpen_le_top).op
          (rightPure integerSkyscraper.obj integerSkyscraper.obj
            integerTheta.hom integerModule.val (Opposite.op ⊤)
            selectedInput (1 : integerSkyscraper.obj.obj (Opposite.op ⊤)))) =
      leftPure integerSkyscraper.obj integerSkyscraper.obj
        integerTheta.hom integerModule.val (Opposite.op selectedOpen)
        (integerSkyscraper.obj.map (homOfLE selectedOpen_le_top).op
          (1 : integerSkyscraper.obj.obj (Opposite.op ⊤)))
        (integerModule.val.map (homOfLE selectedOpen_le_top).op selectedInput) := by
  change (rightSectionIso integerSkyscraper.obj integerSkyscraper.obj integerTheta.hom
      integerModule.val (Opposite.op selectedOpen)).hom
      (rightRestriction integerSkyscraper.obj integerSkyscraper.obj integerTheta.hom
        integerModule.val (homOfLE selectedOpen_le_top).op
        (rightPure integerSkyscraper.obj integerSkyscraper.obj integerTheta.hom
          integerModule.val (Opposite.op ⊤) selectedInput 1)) = _
  have h := rightRestriction_pure integerSkyscraper.obj integerSkyscraper.obj
    integerTheta.hom integerModule.val (homOfLE selectedOpen_le_top).op
    selectedInput (1 : integerSkyscraper.obj.obj (Opposite.op ⊤))
  exact (congrArg (rightSectionIso integerSkyscraper.obj integerSkyscraper.obj
    integerTheta.hom integerModule.val (Opposite.op selectedOpen)).hom h).trans
      (rightSectionIso_pure integerSkyscraper.obj integerSkyscraper.obj
        integerTheta.hom integerModule.val (Opposite.op selectedOpen) _ _)

private noncomputable instance :
    HasWeakSheafify (Opens.grothendieckTopology twoPointSpace) AddCommGrpCat.{0} :=
  opensWeakSheafify twoPointSpace

private noncomputable instance :
    (Opens.grothendieckTopology twoPointSpace).WEqualsLocallyBijective AddCommGrpCat.{0} :=
  opensWEqualsLocallyBijective twoPointSpace

theorem nonemptyProperOpenUnitSquare :
    ((rightPresheafIso integerSkyscraper.obj integerSkyscraper.obj
        integerTheta.hom integerModule.val).hom ≫
      (moduleSheafificationAdjunction integerSkyscraper).unit.app
        (tensorPresheaf integerSkyscraper.obj integerSkyscraper.obj
          integerTheta.hom integerModule.val)).app (Opposite.op selectedOpen)
        ((rightPresheaf integerSkyscraper.obj integerSkyscraper.obj
          integerTheta.hom integerModule.val).map
          (homOfLE selectedOpen_le_top).op
          (rightPure integerSkyscraper.obj integerSkyscraper.obj
            integerTheta.hom integerModule.val (Opposite.op ⊤) selectedInput
            (1 : integerSkyscraper.obj.obj (Opposite.op ⊤)))) =
      ((moduleSheafificationAdjunction integerSkyscraper).unit.app
        (rightPresheaf integerSkyscraper.obj integerSkyscraper.obj
          integerTheta.hom integerModule.val) ≫
        (SheafOfModules.forget (ringSheaf integerSkyscraper) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf integerSkyscraper).obj)).map
          ((rightSheafNatIso integerSkyscraper integerSkyscraper integerTheta).hom.app
            integerModule)).app (Opposite.op selectedOpen)
        ((rightPresheaf integerSkyscraper.obj integerSkyscraper.obj
          integerTheta.hom integerModule.val).map
          (homOfLE selectedOpen_le_top).op
          (rightPure integerSkyscraper.obj integerSkyscraper.obj
            integerTheta.hom integerModule.val (Opposite.op ⊤) selectedInput
            (1 : integerSkyscraper.obj.obj (Opposite.op ⊤)))) := by
  exact congrArg
    (fun morphism => morphism.app (Opposite.op selectedOpen)
      ((rightPresheaf integerSkyscraper.obj integerSkyscraper.obj
        integerTheta.hom integerModule.val).map (homOfLE selectedOpen_le_top).op
        (rightPure integerSkyscraper.obj integerSkyscraper.obj integerTheta.hom
          integerModule.val (Opposite.op ⊤) selectedInput 1)))
    (rightSheafificationUnit_naturality integerSkyscraper integerSkyscraper
      integerTheta integerModule)

/-- Sheaf symmetry also exists over the empty topological space. -/
noncomputable def emptySpaceComparison
    (A B : TopCat.Sheaf CommRingCat.{u} (TopCat.of (PEmpty.{u+1})))
    (theta : A ⟶ B) :
    rightSheafFunctor A B theta ≅ tensorSheafFunctor A B theta :=
  opensRightSheafNatIso A B theta

end Test.ChangeOfRingsSymmetryRoot

#lint-
