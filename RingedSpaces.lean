/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.OpenCover
public import RingedSpaces.InverseImage
public import RingedSpaces.ClosedPointHom
public import RingedSpaces.ClosedPointNonAffine
public import RingedSpaces.ContinuousFunctions
public import RingedSpaces.FiniteRegularityFunctions
public import RingedSpaces.FiniteRegularityFunctions.Maps
public import RingedSpaces.FiniteRegularityFunctions.OpenImmersion
public import RingedSpaces.FiniteRegularityFunctions.LocalBall
public import RingedSpaces.ContinuousFunctions.OpenImmersion
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
public import RingedSpaces.ChartedSpace.SmoothLocalBall
public import RingedSpaces.ChartedSpace.SmoothScalarReconstruction
public import RingedSpaces.ChartedSpace.HolomorphicSections
public import RingedSpaces.Complex.AtlasRegularity
public import RingedSpaces.ChartedSpace.CompatibleAtlases
public import RingedSpaces.ChartedSpace.CompatibleAtlasSheaf

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
When such a map sends a maximal-ideal element to a unit in a nontrivial
commutative ring, the full morphism differs from every affine-induced map.
It provides the sheaf of continuous functions into a topological commutative ring,
stalk evaluation and full ringed-space maps induced by continuous maps,
with contravariant maps on stalks.
For T1 topological fields, its stalks are local and those maps are locally ringed;
open embeddings give open immersions and canonical open-subtype restriction comparisons.
For finite natural regularity orders, it also provides scalar-function sheaves on
charted spaces, with smooth-to-finite section weakening and a zero-order comparison
to the continuous-function sheaf.
For any manifold regularity indexed by `ℕ∞ω`, it provides chart coordinates on
an entire positive-radius model ball. At smooth regularity `∞`, it compares the
canonical smooth scalar locally ringed space restricted from the ambient manifold
with the canonical one on that entire coordinate ball, including the induced
point maps and full-composite germ and section-evaluation laws.
Scalar-preserving morphisms between canonical smooth scalar presheafed spaces
pull back sections by precomposition; for open finite-dimensional targets their
continuous base maps are smooth and determine their full sheaf morphisms.
For real scalars, every morphism preserves constants automatically.
On finite-dimensional complex open domains it also relates holomorphic scalar
representatives to sections of this existing complex-smooth sheaf.
For finite-dimensional boundaryless complex models, differentiable transitions
of a given charted space give analytic (`ω`) and smooth (`∞`) regularity.
Mixed groupoid-compatible atlases on the same topology give own regularity,
equal maximal atlases, and an identity diffeomorphism to a typed copy.
Compatible explicit atlases also give an identity-base comparison of their
canonical smooth scalar locally ringed spaces.
-/
