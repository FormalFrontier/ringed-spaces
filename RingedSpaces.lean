/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.OpenCover
public import RingedSpaces.InverseImage
public import RingedSpaces.ClosedPointHom
public import RingedSpaces.Modules.PresheafChangeOfRings
public import RingedSpaces.Modules.PresheafInverseImage
public import RingedSpaces.Modules.PresheafInverseImageHom
public import RingedSpaces.Modules.SheafChangeOfRings
public import RingedSpaces.Modules.PresheafChangeOfRingsSymmetry
public import RingedSpaces.Modules.SheafChangeOfRingsSymmetry
public import RingedSpaces.Modules.SheafInverseImage
public import RingedSpaces.Modules.SheafInverseImageHom
public import RingedSpaces.Modules.RingedSpacePushforward
public import RingedSpaces.Modules.RingedSpacePullback
public import RingedSpaces.Modules.PullbackCoherence
public import RingedSpaces.Modules.BaseChange
public import RingedSpaces.Modules.BaseChangePasting

/-!
# Ringed spaces

This aggregate import provides restriction maps, literal-intersection compatibility and
open-cover gluing and inverse-image factorization for full morphisms of ringed spaces.
It also exposes same-site extension and restriction of scalars for module
presheaves and sheaves over commutative-ring presheaves and sheaves, including
the naturally equivalent genuine right-factor tensor construction, and the
ordinary inverse image of module presheaves along continuous maps, including
its linear Hom adjunction to native module pushforward. It also exposes the
inverse-image functor for module sheaves along arbitrary continuous maps, its
comparison with underlying additive pullback and the bundled two-sided Hom
adjunction to module-sheaf pushforward. For arbitrary full ringed-space morphisms,
it also exports the original structure-map pushforward and the explicit sheafified
right-tensor pullback, their adjunction and comparison with native pullback.
It further exports coherent identity/composition isomorphisms for these actual
module functors, the push–pull mate of any commutative full-morphism square,
and its horizontal and vertical pasting laws.
It also constructs full morphisms to the spectrum of a commutative local ring
from arbitrary maps to global sections, with constant closed-point base.
-/
