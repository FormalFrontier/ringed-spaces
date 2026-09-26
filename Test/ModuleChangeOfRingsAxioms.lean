/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import all Test.ModuleChangeOfRings
import Test.ModuleChangeOfRingsRoot

/-!
# Transitive axiom audit for module change of rings

The census and generated/private axiom checks use the same `Lean.collectAxioms`
as `#print axioms`. Explicit references to `_proof_` auxiliaries trigger
`linter.auxLemma` because those names are unstable; enumerating their actual
declarations instead keeps this file warning-free without suppressing the linter.
-/

open Lean Elab Command

run_cmd do
  let names := (← getEnv).constants.toList.map Prod.fst |>.filter fun name =>
    (name.toString.splitOn "RingedSpaces.Modules.").length > 1 ||
      (name.toString.splitOn "Test.ModuleChangeOfRings").length > 1
  let mut empty : Nat := 0
  let mut onlyPropext : Nat := 0
  let mut propextQuot : Nat := 0
  let mut allThree : Nat := 0
  let mut otherAllowed : Nat := 0
  let mut printedActualArrow := false
  let mut printedZeroArrow := false
  for name in names.toArray.qsort (fun first second => first.toString < second.toString) do
    let axioms ← Lean.collectAxioms name
    if axioms.any (fun foundAxiom => foundAxiom != `propext &&
        foundAxiom != `Classical.choice && foundAxiom != `Quot.sound) then
      throwError "unapproved axiom in {name}: {axioms}"
    if axioms.isEmpty then
      empty := empty + 1
    else if axioms.size == 1 && axioms.contains `propext then
      onlyPropext := onlyPropext + 1
    else if axioms.size == 2 && axioms.contains `propext && axioms.contains `Quot.sound then
      propextQuot := propextQuot + 1
    else if axioms.size == 3 then
      allThree := allThree + 1
    else
      otherAllowed := otherAllowed + 1
    logInfo m!"CENSUS {name}"
    if name.toString.startsWith "_private." ||
        (name.toString.splitOn "._proof_").length > 1 then
      logInfo m!"AXIOMS '{name}' = {axioms.toList}"
    if name.toString.endsWith "Test.ModuleChangeOfRings.actualTwoObjectArrow" then
      if printedActualArrow then throwError "duplicate private actualTwoObjectArrow"
      logInfo m!"PRINT Test.ModuleChangeOfRings.actualTwoObjectArrow -> {name}: {axioms.toList}"
      printedActualArrow := true
    if name.toString.endsWith "Test.ModuleChangeOfRings.zeroRingArrow" then
      if printedZeroArrow then throwError "duplicate private zeroRingArrow"
      logInfo m!"PRINT Test.ModuleChangeOfRings.zeroRingArrow -> {name}: {axioms.toList}"
      printedZeroArrow := true
  unless printedActualArrow && printedZeroArrow do
    throwError "missing private named test result in full-origin axiom audit"
  logInfo (m!"SUMMARY candidate={names.length} empty={empty} propext={onlyPropext} " ++
    m!"propextQuot={propextQuot} allThree={allThree} otherAllowed={otherAllowed}")
#print axioms RingedSpaces.Modules.Presheaves
#print axioms RingedSpaces.Modules.Sheaves
#print axioms RingedSpaces.Modules.moduleSheafification
#print axioms RingedSpaces.Modules.moduleSheafificationAdjunction
#print axioms RingedSpaces.Modules.opensTensorSheafAdjunction
#print axioms RingedSpaces.Modules.opensWEqualsLocallyBijective
#print axioms RingedSpaces.Modules.opensWeakSheafify
#print axioms RingedSpaces.Modules.presheafTensorUnit
#print axioms RingedSpaces.Modules.restrictionUnit
#print axioms RingedSpaces.Modules.restrictionUnit_apply
#print axioms RingedSpaces.Modules.ringMap
#print axioms RingedSpaces.Modules.ringPresheaf
#print axioms RingedSpaces.Modules.ringSheaf
#print axioms RingedSpaces.Modules.ringSheafMap
#print axioms RingedSpaces.Modules.tensorPresheaf
#print axioms RingedSpaces.Modules.tensorPresheafAdjunction
#print axioms RingedSpaces.Modules.tensorPresheafAdjunction_counit
#print axioms RingedSpaces.Modules.tensorPresheafAdjunction_unit
#print axioms RingedSpaces.Modules.tensorPresheafFunctor
#print axioms RingedSpaces.Modules.tensorPresheafHomDown
#print axioms RingedSpaces.Modules.tensorPresheafHomDown_naturality_left
#print axioms RingedSpaces.Modules.tensorPresheafHomDown_naturality_right
#print axioms RingedSpaces.Modules.tensorPresheafHomEquiv
#print axioms RingedSpaces.Modules.tensorPresheafHomUp
#print axioms RingedSpaces.Modules.tensorPresheafHomUp_smul
#print axioms RingedSpaces.Modules.tensorPresheafMap
#print axioms RingedSpaces.Modules.tensorRestriction
#print axioms RingedSpaces.Modules.tensorRestriction_smul
#print axioms RingedSpaces.Modules.tensorRestriction_unit
#print axioms RingedSpaces.Modules.tensorSection
#print axioms RingedSpaces.Modules.tensorSectionHomEquiv
#print axioms RingedSpaces.Modules.tensorSectionHomEquiv_apply
#print axioms RingedSpaces.Modules.tensorSectionHomEquiv_symm_unit
#print axioms RingedSpaces.Modules.tensorSectionMap
#print axioms RingedSpaces.Modules.tensorSectionMap_smul
#print axioms RingedSpaces.Modules.tensorSectionMap_unit
#print axioms RingedSpaces.Modules.tensorSheaf
#print axioms RingedSpaces.Modules.tensorSheafAdjunction
#print axioms RingedSpaces.Modules.tensorSheafAdjunction_counit
#print axioms RingedSpaces.Modules.tensorSheafAdjunction_unit
#print axioms RingedSpaces.Modules.tensorSheafFunctor
#print axioms RingedSpaces.Modules.tensorSheafHomEquiv
#print axioms RingedSpaces.Modules.tensorSheafHomEquiv_apply
#print axioms RingedSpaces.Modules.tensorSheafHomEquiv_naturality_left
#print axioms RingedSpaces.Modules.tensorSheafHomEquiv_naturality_right
#print axioms RingedSpaces.Modules.tensorSheafHomEquiv_val
#print axioms RingedSpaces.Modules.tensorUnitSection
#print axioms Test.ModuleChangeOfRings.adjunctionCounitOnScalars
#print axioms Test.ModuleChangeOfRings.adjunctionUnitOnSections
#print axioms Test.ModuleChangeOfRings.emptySiteAdjunction
#print axioms Test.ModuleChangeOfRings.emptySpaceAdjunction
#print axioms Test.ModuleChangeOfRings.fullRingNaturality
#print axioms Test.ModuleChangeOfRings.homInverses
#print axioms Test.ModuleChangeOfRings.homNaturalityLeft
#print axioms Test.ModuleChangeOfRings.homNaturalityRight
#print axioms Test.ModuleChangeOfRings.nontrivialArrowRestriction
#print axioms Test.ModuleChangeOfRings.sheafAdjunctionCounitNaturality
#print axioms Test.ModuleChangeOfRings.sheafAdjunctionUnitNaturality
#print axioms Test.ModuleChangeOfRings.sheafCounitGenerator
#print axioms Test.ModuleChangeOfRings.sheafHomInverses
#print axioms Test.ModuleChangeOfRings.sheafHomNaturalityLeft
#print axioms Test.ModuleChangeOfRings.sheafHomNaturalityRight
#print axioms Test.ModuleChangeOfRings.sheafHomOnGenerator
#print axioms Test.ModuleChangeOfRings.sheafUnitGenerator
#print axioms Test.ModuleChangeOfRings.tensorFunctorIdentityComposition
#print axioms Test.ModuleChangeOfRings.tensorMapArbitraryScalar
#print axioms Test.ModuleChangeOfRings.topologicalAdjunction
#print axioms Test.ModuleChangeOfRings.zeroRingPresheaf
#print axioms Test.ModuleChangeOfRingsRoot.scalarRestriction
#print axioms Test.ModuleChangeOfRingsRoot.topologicalSheafAdjunction

#print axioms ModuleCat.extendScalars
#print axioms ModuleCat.extendRestrictScalarsAdj
#print axioms ModuleCat.ExtendScalars.hom_ext
#print axioms PresheafOfModules.sheafification
#print axioms PresheafOfModules.sheafificationHomEquiv
#print axioms PresheafOfModules.sheafificationAdjunction
#print axioms PresheafOfModules.restrictScalars
#print axioms SheafOfModules.restrictScalars
#print axioms SheafOfModules.fullyFaithfulForget
#print axioms CategoryTheory.Adjunction.mkOfHomEquiv
