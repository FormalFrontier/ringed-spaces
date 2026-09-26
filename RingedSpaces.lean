/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.OpenCover
public import RingedSpaces.InverseImage
public import RingedSpaces.Modules.PresheafChangeOfRings
public import RingedSpaces.Modules.PresheafInverseImage
public import RingedSpaces.Modules.PresheafInverseImageHom
public import RingedSpaces.Modules.SheafChangeOfRings
public import RingedSpaces.Modules.PresheafChangeOfRingsSymmetry
public import RingedSpaces.Modules.SheafChangeOfRingsSymmetry

/-!
# Ringed spaces

This aggregate import provides restriction maps, literal-intersection compatibility and
open-cover gluing and inverse-image factorization for full morphisms of ringed spaces.
It also exposes same-site extension and restriction of scalars for module
presheaves and sheaves over commutative-ring presheaves and sheaves, including
the naturally equivalent genuine right-factor tensor construction, and the
ordinary inverse image of module presheaves along continuous maps, including
its linear Hom adjunction to native module pushforward.
-/
