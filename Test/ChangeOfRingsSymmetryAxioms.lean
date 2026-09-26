/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import all Test.ChangeOfRingsSymmetry
import all Test.ChangeOfRingsSymmetryFixture
import all Test.ChangeOfRingsSymmetryRoot

/-!
# Pinned transitive axiom census for right-factor scalar extension

This driver prints every declaration (including generated and private ones) from
the five new imported Lean modules by imported module index, then checks its
own declarations and explicitly prints the public API, critical native endpoints
and named consumer axioms.
-/

open Lean Elab Command

#list_linters

run_cmd do
  let env ← getEnv
  let moduleNames := #[`RingedSpaces.Modules.PresheafChangeOfRingsSymmetry,
    `RingedSpaces.Modules.SheafChangeOfRingsSymmetry,
    `Test.ChangeOfRingsSymmetry, `Test.ChangeOfRingsSymmetryFixture,
    `Test.ChangeOfRingsSymmetryRoot]
  let mut total : Nat := 0
  let mut noAxioms : Nat := 0
  let mut allowedAxioms : Nat := 0
  let mut printedTwoObject := false
  let mut printedVaryingRestriction := false
  for moduleName in moduleNames do
    let some moduleIdx := env.getModuleIdx? moduleName
      | throwError "missing audit module {moduleName}"
    let names := (env.constants.toList.map Prod.fst).filter fun declaration =>
      env.getModuleIdxFor? declaration == some moduleIdx
    logInfo m!"MODULE {moduleName} DECLARATIONS {names.length}"
    total := total + names.length
    for declaration in names.toArray.qsort
        (fun first second => first.toString < second.toString) do
      let axioms ← Lean.collectAxioms declaration
      if axioms.any (fun foundAxiom => foundAxiom != `propext &&
          foundAxiom != `Classical.choice && foundAxiom != `Quot.sound) then
        throwError "unapproved axiom in {declaration}: {axioms}"
      if axioms.isEmpty then
        noAxioms := noAxioms + 1
      else
        allowedAxioms := allowedAxioms + 1
      logInfo m!"AXIOMS '{declaration}' = {axioms.toList}"
      if declaration.toString.endsWith "Test.ChangeOfRingsSymmetry.twoObjectArrowClient" then
        if printedTwoObject then throwError "duplicate private twoObjectArrowClient"
        logInfo m!"PRINT Test.ChangeOfRingsSymmetry.twoObjectArrowClient -> {declaration}: {axioms.toList}"
        printedTwoObject := true
      if declaration.toString.endsWith
          "Test.ChangeOfRingsSymmetryFixture.varyingRestrictionOnTwo" then
        if printedVaryingRestriction then throwError "duplicate private varyingRestrictionOnTwo"
        logInfo m!"PRINT Test.ChangeOfRingsSymmetryFixture.varyingRestrictionOnTwo -> {declaration}: {axioms.toList}"
        printedVaryingRestriction := true
  unless printedTwoObject && printedVaryingRestriction do
    throwError "missing private named symmetry result in full-origin axiom audit"
  logInfo m!"SUMMARY declarations={total} empty={noAxioms} allowed={allowedAxioms}"
#print axioms TensorProduct.comm
#print axioms TensorProduct.comm_tmul
#print axioms TensorProduct.comm_symm_tmul
#print axioms TensorProduct.map_comm
#print axioms TensorProduct.inductionOn
#print axioms AddEquiv.module
#print axioms AddEquiv.linearEquiv
#print axioms LinearEquiv.isScalarTower
#print axioms ModuleCat.ExtendScalars.smul_tmul
#print axioms PresheafOfModulesOfCommRing.isoMk
#print axioms skyscraperSheaf
#print axioms SheafOfModules.unit
#print axioms PresheafOfModules.unit
#print axioms Int.castRingHom.eq_1
#print axioms RingedSpaces.Modules.tensorRestriction
#print axioms RingedSpaces.Modules.tensorPresheafFunctor
#print axioms RingedSpaces.Modules.tensorPresheafHomUp_smul
#print axioms RingedSpaces.Modules.moduleSheafification
#print axioms RingedSpaces.Modules.moduleSheafificationAdjunction
#print axioms RingedSpaces.Modules.tensorSheafFunctor
#print axioms RingedSpaces.Modules.rightFactor
#print axioms RingedSpaces.Modules.rightSection
#print axioms RingedSpaces.Modules.rightSectionAddEquiv
#print axioms RingedSpaces.Modules.rightModule
#print axioms RingedSpaces.Modules.rightSectionCat
#print axioms RingedSpaces.Modules.rightSectionIso
#print axioms RingedSpaces.Modules.rightPure
#print axioms RingedSpaces.Modules.leftPure
#print axioms RingedSpaces.Modules.rightSectionIso_pure
#print axioms RingedSpaces.Modules.rightSectionIso_inv_tmul
#print axioms RingedSpaces.Modules.rightSectionSmul
#print axioms RingedSpaces.Modules.smul_pure
#print axioms RingedSpaces.Modules.rightASmul_pure
#print axioms RingedSpaces.Modules.rightBalance_pure
#print axioms RingedSpaces.Modules.theta_smul_pure
#print axioms RingedSpaces.Modules.theta_smul
#print axioms RingedSpaces.Modules.unit_eq_leftPure
#print axioms RingedSpaces.Modules.leftPure_eq_smul_unit
#print axioms RingedSpaces.Modules.rightRestriction
#print axioms RingedSpaces.Modules.rightRestriction_comm
#print axioms RingedSpaces.Modules.oppositeRestriction_pure
#print axioms RingedSpaces.Modules.rightRestriction_pure
#print axioms RingedSpaces.Modules.rightRestriction_semilinear
#print axioms RingedSpaces.Modules.rightPresheaf
#print axioms RingedSpaces.Modules.rightPresheafIso
#print axioms RingedSpaces.Modules.rightPresheafMap
#print axioms RingedSpaces.Modules.oppositeMap_pure
#print axioms RingedSpaces.Modules.rightSectionMap
#print axioms RingedSpaces.Modules.rightSectionMap_pure
#print axioms RingedSpaces.Modules.rightPresheafMap_pure
#print axioms RingedSpaces.Modules.rightPresheafMap_restriction
#print axioms RingedSpaces.Modules.rightUnitSection
#print axioms RingedSpaces.Modules.rightUnitSection_pure
#print axioms RingedSpaces.Modules.rightPresheafUnit
#print axioms RingedSpaces.Modules.rightPresheafUnit_pure
#print axioms RingedSpaces.Modules.rightPresheafFunctor
#print axioms RingedSpaces.Modules.rightPresheafNatIso
#print axioms RingedSpaces.Modules.rightSheafFunctor
#print axioms RingedSpaces.Modules.rightSheafNatIso
#print axioms RingedSpaces.Modules.rightSheafificationUnit_naturality
#print axioms RingedSpaces.Modules.opensRightSheafNatIso
#print axioms Test.ChangeOfRingsSymmetry.arbitraryCoefficients
#print axioms Test.ChangeOfRingsSymmetry.balanceForFullMap
#print axioms Test.ChangeOfRingsSymmetry.arbitraryTensorCompatibility
#print axioms Test.ChangeOfRingsSymmetry.comparisonBothDirections
#print axioms Test.ChangeOfRingsSymmetry.actualArrowRestriction
#print axioms Test.ChangeOfRingsSymmetry.arbitraryMorphismNaturality
#print axioms Test.ChangeOfRingsSymmetry.rightFunctorLaws
#print axioms Test.ChangeOfRingsSymmetry.rightIdentityOnPure
#print axioms Test.ChangeOfRingsSymmetry.unitAndComparison
#print axioms Test.ChangeOfRingsSymmetry.homFormulaViaComparison
#print axioms Test.ChangeOfRingsSymmetry.emptySiteComparison
#print axioms Test.ChangeOfRingsSymmetry.zeroRingPresheaf
#print axioms Test.ChangeOfRingsSymmetry.zeroRingArrowComparison
#print axioms Test.ChangeOfRingsSymmetry.sheafificationComparisonSquare
#print axioms Test.ChangeOfRingsSymmetryFixture.changingRing
#print axioms Test.ChangeOfRingsSymmetryFixture.constantIntegers
#print axioms Test.ChangeOfRingsSymmetryFixture.integerInclusion
#print axioms Test.ChangeOfRingsSymmetryFixture.nonidentityComponentOnTwo
#print axioms Test.ChangeOfRingsSymmetryFixture.integerInclusionNotSurjective
#print axioms Test.ChangeOfRingsSymmetryFixture.nontrivialTwoCoefficientRestriction
#print axioms Test.ChangeOfRingsSymmetryRoot.rootComparisonOnArbitraryCoefficient
#print axioms Test.ChangeOfRingsSymmetryRoot.rootNonidentityDiagram
#print axioms Test.ChangeOfRingsSymmetryRoot.emptyOpenIsProper
#print axioms Test.ChangeOfRingsSymmetryRoot.properOpenRestrictionAndSheafification
#print axioms Test.ChangeOfRingsSymmetryRoot.twoPointSheafComparison
#print axioms Test.ChangeOfRingsSymmetryRoot.selectedOpen_nonempty
#print axioms Test.ChangeOfRingsSymmetryRoot.selectedOpen_proper
#print axioms Test.ChangeOfRingsSymmetryRoot.integerSkyscraper
#print axioms Test.ChangeOfRingsSymmetryRoot.integerModule
#print axioms Test.ChangeOfRingsSymmetryRoot.selectedInput_ne_zero
#print axioms Test.ChangeOfRingsSymmetryRoot.nonemptyProperOpenComparison
#print axioms Test.ChangeOfRingsSymmetryRoot.nonemptyProperOpenUnitSquare
#print axioms Test.ChangeOfRingsSymmetryRoot.emptySpaceComparison

run_cmd do
  let env ← getEnv
  let declarations := (env.constants.toList.map Prod.fst).filter fun declaration =>
    (env.getModuleIdxFor? declaration).isNone
  logInfo m!"MODULE Test.ChangeOfRingsSymmetryAxioms CURRENT DECLARATIONS {declarations.length}"
  for declaration in declarations.toArray.qsort
      (fun first second => first.toString < second.toString) do
    let axioms ← Lean.collectAxioms declaration
    if axioms.any (fun foundAxiom => foundAxiom != `propext &&
        foundAxiom != `Classical.choice && foundAxiom != `Quot.sound) then
      throwError "unapproved axiom in {declaration}: {axioms}"
    logInfo m!"AXIOMS '{declaration}' = {axioms.toList}"

#lint-
