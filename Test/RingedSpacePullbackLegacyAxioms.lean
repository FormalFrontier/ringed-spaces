/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import all Test.RingedSpacePullbackLegacy

set_option warningAsError true

/-! Compiled-origin audit of the native client with the historical filename. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleName := `Test.RingedSpacePullbackLegacy
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
    logInfo m!"CENSUS {moduleName}::{name}: {axioms.toList}"
  for name in env.header.moduleData[index.toNat]!.extraConstNames do
    if (env.find? name).isSome then
      throwError "unlisted kernel constant in extra IR names: {moduleName}::{name}"
    logInfo m!"EXTRA_IR_ORIGIN {moduleName}::{name}"

#print axioms Test.RingedSpacePullbackLegacy.legacyAdjunction

#lint
