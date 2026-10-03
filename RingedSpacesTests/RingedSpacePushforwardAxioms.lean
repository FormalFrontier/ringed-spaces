/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import all RingedSpaces.Modules.RingedSpacePushforward
import all RingedSpacesTests.RingedSpacePushforward
import all RingedSpacesTests.RingedSpacePushforwardConcrete
import all RingedSpacesTests.RingedSpacePushforwardRootCoexist

set_option warningAsError true

/-!
# Pinned module-origin axiom audit

The census includes compiled kernel constants from every new native module,
including generated and private proofs. Imported dependencies are checked
transitively by `collectAxioms`, rather than recounted as new source declarations.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules : List Name :=
    [`RingedSpaces.Modules.RingedSpacePushforward,
     `RingedSpacesTests.RingedSpacePushforward,
     `RingedSpacesTests.RingedSpacePushforwardConcrete,
     `RingedSpacesTests.RingedSpacePushforwardRootCoexist]
  let mut total : Nat := 0
  let mut empty : Nat := 0
  let mut extra : Nat := 0
  for moduleName in modules do
    let some index := env.getModuleIdx? moduleName
      | throwError "missing compiled module: {moduleName}"
    let names := env.constants.toList.map Prod.fst |>.filter fun name =>
      env.getModuleIdxFor? name == some index
    if names.isEmpty then
      throwError "no compiled declarations from {moduleName}"
    logInfo m!"MODULE {moduleName}: compiled={names.length}"
    for name in names.toArray.qsort (fun first second => first.toString < second.toString) do
      let axioms ← Lean.collectAxioms name
      if axioms.any (fun foundAxiom => foundAxiom != `propext &&
          foundAxiom != `Classical.choice && foundAxiom != `Quot.sound) then
        throwError "unapproved axiom in {moduleName}::{name}: {axioms}"
      if axioms.isEmpty then
        empty := empty + 1
      total := total + 1
      logInfo m!"CENSUS {moduleName}::{name}: {axioms.toList}"
    let additionalNames := env.header.moduleData[index.toNat]!.extraConstNames
    for name in additionalNames do
      if (env.find? name).isSome then
        throwError "unlisted kernel constant in extra IR names: {moduleName}::{name}"
      extra := extra + 1
      logInfo m!"EXTRA_IR_ORIGIN {moduleName}::{name}"
  logInfo m!"SUMMARY compiled={total} noAxioms={empty} allowedOnly={total - empty} extraIR={extra}"

#print axioms RingedSpaces.Modules.RingedSpacePushforward.ringSheaf
#print axioms RingedSpaces.Modules.RingedSpacePushforward.ringSheafMap
#print axioms RingedSpaces.Modules.RingedSpacePushforward.structureMap
#print axioms RingedSpaces.Modules.RingedSpacePushforward.pushforwardFunctor
#print axioms RingedSpaces.Modules.RingedSpacePushforward.actualUnit_comp_ringSheafMap
#print axioms RingedSpaces.Modules.RingedSpacePushforward.restrictPushforwardIso
#print axioms RingedSpaces.Modules.RingedSpacePushforward.structureMap_apply
#print axioms RingedSpaces.Modules.RingedSpacePushforward.structureMap_original
#print axioms RingedSpaces.Modules.RingedSpacePushforward.restrictPushforwardIso_hom_app
#print axioms RingedSpaces.Modules.RingedSpacePushforward.restrictPushforwardIso_inv_app
#print axioms RingedSpaces.Modules.RingedSpacePushforward.restrictPushforwardIso_smul
#print axioms RingedSpaces.Modules.RingedSpacePushforward.restrictPushforwardIso_inv_smul
#print axioms RingedSpaces.Modules.RingedSpacePushforward.restrictPushforwardIso_naturality
#print axioms RingedSpaces.Modules.RingedSpacePushforward.restrictPushforwardIso_naturality_apply
#print axioms RingedSpaces.Modules.RingedSpacePushforward.restrictPushforwardIso_inverseLaws

#print axioms Test.RingedSpacePushforward.completeMap
#print axioms Test.RingedSpacePushforward.actualOpen
#print axioms Test.RingedSpacePushforward.comparison
#print axioms Test.RingedSpacePushforward.forwardOpen
#print axioms Test.RingedSpacePushforward.backwardOpen
#print axioms Test.RingedSpacePushforward.natural
#print axioms Test.RingedSpacePushforwardConcrete.properAndNonidentity
#print axioms Test.RingedSpacePushforwardConcrete.properOpenActualMap
#print axioms Test.RingedSpacePushforwardConcrete.properOpenFullMate
#print axioms Test.RingedSpacePushforwardConcrete.properOpenForward
#print axioms Test.RingedSpacePushforwardConcrete.emptyTargetOpen
#print axioms Test.RingedSpacePushforwardConcrete.zeroRingBoundary
#print axioms Test.RingedSpacePushforwardRootCoexist.fullMap

#lint
