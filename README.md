# Ringed Spaces

License: Apache-2.0 (see `LICENSE`).
Authors: Formal Frontier Agents (see `NOTICE.md` for individual contributors and retained upstream notices).

A Lean library for restricting, gluing and factoring **full ringed-space morphisms**.
The open-cover construction uses mathlib's sheafed-space glue data and proves
that the glued object is the original ringed space. The intersection bridge
identifies the literal restriction to `U ⊓ V` with the categorical pullback
of restrictions to `U` and `V`. Equalities include maps of structure sheaves,
not just underlying continuous maps. The library also develops same-site
scalar extension for module presheaves and sheaves, continuous inverse images
of module presheaves, right-factor tensor comparison and a concrete Hom
adjunction to native pushforward.
The aggregate `RingedSpaces` exports continuous inverse images of module
sheaves and their bundled Hom adjunction, as well as full-morphism pushforward
and explicit right-tensor pullback with its adjunction and native comparison.
It also exports module pullback identity/composition coherence and the mate
associated to any commutative square of full ringed-space morphisms, including
horizontal and vertical pasting laws for the actual outer-square mate.
Their mathematical leaves received bounded preparation acceptances. Separate
revision-specific review and integration records govern the combined
root/default-target assembly; the earlier assembly was published in a prior
release. The module-coherence and square-mate transfer has its own review and
release boundary, independent of source-level coverage.
For a commutative local ring, the library also constructs full ringed-space
morphisms with constant closed-point base from arbitrary maps into global
sections. This destination contribution has received independent review and
maintainer acceptance; release publication is recorded separately for each
exact artifact.

## API

Import `RingedSpaces.Restriction` for open-restriction maps and the intersection
pullback; import `RingedSpaces.OpenCover` for the gluing bridge; import
`RingedSpaces.InverseImage` for inverse-image factorization, or use the aggregate
`RingedSpaces`.
Import `RingedSpaces.Modules.PresheafInverseImage` for inverse-image module
presheaves along continuous maps; see `docs/presheaf-inverse-image.md` for the
actual coefficient ring, generator, functor, unit and additive comparison APIs.
Import `RingedSpaces.Modules.PresheafInverseImageHom` for the concrete functor's
bundled linear `homEquiv f R M N` and `adjunction f R` to the native module
pushforward; `forward_apply`, `backward_ι`, `backward_smul`, `unit_apply`,
`counit_ι` and `forward_underlying_additive` expose formulas. See the
[standalone mathematical API](docs/presheaf-inverse-image-hom.md) and
[contributor and source attribution](NOTICE.md).
The aggregate `RingedSpaces` exposes the module-sheaf API, as does the direct
import `RingedSpaces.Modules.SheafInverseImageHom`; the narrower direct import
`RingedSpaces.Modules.SheafInverseImage` exposes its functor and comparison.
See the [sheaf inverse-image guide](docs/sheaf-inverse-image.md) and the
[root-only checked client](Test/SheafInverseImageRoot.lean).
For arbitrary full ringed-space morphisms, import `RingedSpaces` or
`RingedSpaces.Modules.RingedSpacePushforward` for the original structure map,
actual inverse-image mate and natural full pushforward comparison; see the
[pushforward guide](docs/ringed-space-pushforward.md). Import `RingedSpaces` or
`RingedSpaces.Modules.RingedSpacePullback` for the explicit sheafified right-tensor
pullback, Hom adjunction, unit and comparison with native pullback; see the
[pullback guide](docs/ringed-space-pullback.md) and the
[root-only full-morphism client](Test/RingedSpaceFullMorphismRoot.lean).
For coherent module functors and square comparisons, import `RingedSpaces`, or
the narrower `RingedSpaces.Modules.PullbackCoherence` and
`RingedSpaces.Modules.BaseChange` and
`RingedSpaces.Modules.BaseChangePasting` leaves; see the
[coherence/base-change guide](docs/ringed-module-coherence-base-change.md),
[pasting guide](docs/ringed-module-base-change-pasting.md),
[root-only square client](Test/RingedSpaceBaseChange.lean) and
[pasting client](Test/RingedSpaceBaseChangePasting.lean).
For a commutative local ring `R`, import `RingedSpaces` or the narrower
`RingedSpaces.ClosedPointHom` to construct a full morphism from any
`R →+* X.presheaf.obj (op ⊤)` with underlying map constant at the closed point.
The `AlgebraicGeometry.RingedSpace.ClosedPointHom` namespace provides `hom`,
`hom_top_transport`, fixed-base `ext` and `equiv`, and `comp_hom` for
precomposition. The [mathematical guide](docs/closed-point-hom.md) explains
the assumptions and the [root-only client](Test/ClosedPointHom.lean) checks
the arbitrary, empty and field cases, including a conditional nonlocal example.
This is a *full ringed-space morphism*, not generally a locally ringed-space or
scheme morphism.
All declarations below are in `AlgebraicGeometry.RingedSpace`:

- `restrictMap U V h` for `h : U ≤ V`: the canonical **full** morphism
  `X.restrict U.isOpenEmbedding ⟶ X.restrict V.isOpenEmbedding`. Its full
  factorization `restrictMap_ofRestrict` and pointwise inclusion
  `restrictMap_base` determine its sheaf and carrier behavior. `restrictMap_id`
  and `restrictMap_comp` provide identity and composition laws.
- `isPullback_restrictInf U V`: the full pullback square from
  `X.restrict (U ⊓ V).isOpenEmbedding` to the two canonical restrictions;
  `IsPullback.isoPullback` compares it to any chosen categorical pullback.
- `OpenCover X`: an indexed family `U : J → Opens X` with `covers : ∀ x, ∃ i, x ∈ U i`.
- `OpenCover.obj i`: the canonical restriction `X.restrict (U i).isOpenEmbedding`.
- `OpenCover.ι i`: the full canonical morphism `X.ofRestrict (U i).isOpenEmbedding`.
- `OpenCover.glueMorphisms f hf`: a full morphism `X ⟶ Y` for compatible morphisms
  `f i : C.obj i ⟶ Y`. Compatibility `hf i j` identifies their composites with
  `pullback.fst (C.ι i) (C.ι j)` and `pullback.snd (C.ι i) (C.ι j)`.
- `OpenCover.ι_glueMorphisms f hf i`: `C.ι i ≫ C.glueMorphisms f hf = f i`.
- `OpenCover.hom_ext f g h`: equality of full morphisms whose restrictions coincide.
- `OpenCover.existsUnique_gluing f hf`: exactly one morphism with these restrictions.
- `OpenCover.pullback_compatibility_iff_intersection f`: agreement on categorical
  pullbacks iff agreement after the full canonical maps from literal intersections.
- `OpenCover.existsUnique_gluing_of_intersection f hf`: the *existing* unique
  global extension, now taking literal intersection compatibility `hf` directly.
- `inverseImage Y g` for `Y : RingedSpace.{u,u}` and any continuous map
  `g : T ⟶ Y.carrier`, `T : TopCat.{u}`: a ringed space with *literal* carrier
  `T` and native sheaf `(TopCat.Sheaf.pullback CommRingCat g).obj Y.sheaf`.
  It depends only on `Y` and `g`, not on a ringed-space structure on `T`.
- `ofInverseImage Y g : inverseImage Y g ⟶ Y`: the **full** canonical morphism
  over `g`, whose sheaf component is the inverse-image/pushforward adjunction unit.
- `inverseImageMap f : (inverseImage Y f.hom.base).sheaf ⟶ X.sheaf`, for a
  full `f : X ⟶ Y`: the sheaf-adjunction mate of `f`'s entire ring-sheaf map.
  `inverseImageMap_unit` is the full sheaf equation;
  `inverseImageMap_unit_hom`, `inverseImageMap_unit_app` and
  `inverseImageMap_unit_components` recover the given
  presheaf map and its ring homomorphism on **every** target open.
- `toInverseImage f : X ⟶ inverseImage Y f.hom.base`: the full map over the
  identity on `X`; `toInverseImage_c`, `toInverseImage_c_app` and
  `toInverseImage_c_app_eq` expose its
  identity-pushforward transport. The full-morphism equality
  `toInverseImage_ofInverseImage f` asserts
  `toInverseImage f ≫ ofInverseImage Y f.hom.base = f`.

The `inverseImage_*` and `ofInverseImage_*` carrier/sheaf/base/component lemmas
expose the construction without unfolding implementation details. This is a
sheaf inverse image, **not** a categorical fiber-product pullback. The
following self-contained example and the additional literal-intersection and
module-adjunction examples are checked in `RingedSpacesExamples.lean` and built
by the default Lake target:

```lean
module

public import RingedSpaces

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

example {X Y : RingedSpace.{u, u}} (C : RingedSpace.OpenCover X)
    (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) :
    ∃! global : X ⟶ Y, ∀ i, C.ι i ≫ global = f i :=
  C.existsUnique_gluing f hf
```

The restriction, gluing and inverse-image APIs use **diagonal universes**
`X Y : RingedSpace.{u,u}`, `T : TopCat.{u}` and, for covers, `J : Type u`.
No mixed-universe lifting is claimed. Those APIs require no local-ring, scheme,
finite-cover, nonempty-cover, nonempty-member, or nonzero-ring hypothesis.
The constant-closed construction separately requires `[IsLocalRing R]` for its
target coefficient ring `R`. The index family may be empty when `X` is empty; see
`Test/OpenCover.lean` and `Test/Restriction.lean` for empty and infinite-cover
downstream clients. Literal intersections may be empty, even for nonempty opens.
`Test/InverseImage.lean` also exercises a zero-ring sheaf on a two-point space
with a nonidentity continuous base map and an empty underlying source.

## Module Change of Rings

Import `RingedSpaces.Modules.PresheafChangeOfRings` for a functorial tensor
presheaf and its adjunction, or `RingedSpaces.Modules.SheafChangeOfRings` for
the sheafified construction. Both are also available through `RingedSpaces`.
For `A B : Cᵒᵖ ⥤ CommRingCat.{u}` and a *full* `theta : A ⟶ B`, the
`RingedSpaces.Modules.tensorPresheafFunctor A B theta` has section
`B(U) ⊗[A(U)] M(U)` and is left adjoint to
`PresheafOfModules.restrictScalars (RingedSpaces.Modules.ringMap A B theta)`.
Its `tensorRestriction_smul`, `tensorSectionMap_smul`,
`tensorPresheafHomUp_smul`, `tensorPresheafAdjunction_unit` and
`tensorPresheafAdjunction_counit` expose the action on arbitrary coefficients
and on generators. The presheaf construction needs neither a topology nor a
sheaf condition, and supports independent universes for site objects and
morphisms; the ring and module carrier universe is shared.

For `A B : Sheaf J CommRingCat.{u}`, `tensorSheafFunctor A B theta` sheafifies
the tensor presheaf using native `PresheafOfModules.sheafification` and is left
adjoint to `SheafOfModules.restrictScalars` along the **whole** `theta`.
The required site witnesses are `HasWeakSheafify J AddCommGrpCat.{u}`,
`J.WEqualsLocallyBijective AddCommGrpCat.{u}` and
`J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})`. The last witness
preserves the ring sheaf when forgetting commutativity on arbitrary large
sites. `opensTensorSheafAdjunction` derives these instances for a topological
open site at diagonal universes, without a nonempty-space hypothesis. Arbitrary
open sections of the sheafification are **not** asserted to be raw tensors;
`tensorSheafAdjunction_unit` and `tensorSheafAdjunction_counit` give equations
only on the genuine sheafification-unit generators. See
[`docs/module-change-of-rings.md`](docs/module-change-of-rings.md) for the
mathematical argument, assumptions and additional APIs.

## Module Presheaf Inverse Image

The ordinary inverse image of module presheaves along continuous
maps is documented in [`docs/presheaf-inverse-image.md`](docs/presheaf-inverse-image.md).

## Module Sheaf Inverse Image

The root-exported `SheafInverseImage.moduleFunctor f S` sheafifies the actual
neighborhood-colimit module presheaf and restricts scalars along the genuine
comparison between the forgotten `CommRingCat` and native `RingCat` sheaf
pullbacks. `comparison_unit` and `ringUnit_iso` identify complete ring-sheaf
units, not merely their values on selected sections. `actualUnit` uses the
actual commutative-ring pullback unit; `homEquiv` gives bundled linear module-
sheaf maps, natural in both variables, and `adjunction` packages their unit,
counit and triangle equations. `moduleUnderlyingNatIso`,
`forward_underlying_additive`, `backward_underlying_additive` and
`unit_underlying` identify whole underlying additive sheaf morphisms. See
[`docs/sheaf-inverse-image.md`](docs/sheaf-inverse-image.md) for types and limits.
The sheaf mathematical leaves and prior reader documentation received bounded
owner acceptances as preparation. These do not independently accept the
September 26, 2026 combined assembly, its release or source coverage.

## Full Ringed-Space Module Morphisms

The root-exported `RingedSpacePushforward.structureMap f` is the forgotten
**original** full structure map of any `f : X ⟶ Y`, including its ring maps on
every target open; `actualUnit_comp_ringSheafMap` identifies its mate and
`restrictPushforwardIso` naturally compares the two module pushforwards.
`RingedSpacePullback.pullbackFunctor f` sheafifies the genuine right-factor
tensor after continuous module inverse image. Its `homEquiv` and `adjunction`
give an adjunction to full pushforward, while `unit_formula` and
`nativeComparison_unit`, `nativeComparison_counit`, and
`nativeComparison_homEquiv` check the unit and adjunction-level native bridge.
No raw tensor formula on arbitrary opens or stalk-locality assumption is used.
The [root-only client](Test/RingedSpaceFullMorphismRoot.lean) checks the public
aggregate without leaf imports. The two `RootCoexist` clients additionally
test root-plus-direct compatibility; they are not root-only witnesses.

## Module Pullback Coherence and Square Mates

For composable full ringed-space morphisms, `PullbackCoherence.pushforwardComp`
and `pullbackComp` compare direct and right-tensor inverse images by oriented
natural isomorphisms; `pushforwardId` and `pullbackId` handle identities. Their
unit, associativity and adjunction-mate laws use the actual functors and
adjunction, not definitional equality. `BaseChange.pushPull` supplies a natural
push–pull transformation for **any** commutative square, with a unit/transpose
characterization, uniqueness, sectionwise linearity and restriction compatibility.
The identity-vertical square normalizes to the identity; a non-Cartesian empty
corner over the zero ring exercises the lack of Cartesian assumptions. No
general invertibility, flatness or raw-section formula is claimed. See the
[standalone guide](docs/ringed-module-coherence-base-change.md).
`BaseChange.pushPull_pastePullback` and `pushPull_pastePushforward` identify
the actual outer-square mate with the composite of the two constituent mates,
using canonical inverse-/direct-image composition isomorphisms and functor
associators. They need only the two square-commutativity hypotheses; see the
[pasting guide](docs/ringed-module-base-change-pasting.md).

## Right-Factor Scalar Extension

The genuine section tensor `M(U) ⊗[A(U)] B(U)` carries the `B(U)` action on
the right factor and is naturally isomorphic to the existing sectionwise
extension `B(U) ⊗[A(U)] M(U)`. The construction extends to module presheaves
and, after sheafification, module sheaves without claiming raw-tensor sections
on arbitrary opens. See [`docs/change-of-rings-symmetry.md`](docs/change-of-rings-symmetry.md).

## Build

Use the repository's `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`) and
`lakefile.toml`, which pins the sole direct dependency mathlib to
`83abb3e776bdefcbc447a1e44d0debe4010039e5`:

```sh
lake exe cache get
lake --wfail build
```

The 45 literal `defaultTargets` include the aggregate library, stored
examples and all 43 shipped `Test` modules: direct, concrete, audit,
root-only, root-plus-direct coexistence, and intentional legacy clients.
`Test.SheafInverseImageRoot`, `Test.RingedSpaceFullMorphismRoot`,
`Test.RingedSpaceBaseChange` and `Test.ClosedPointHom` import **only** the
public aggregate as their project import. The `RootCoexist` clients retain explicit leaf imports as
compatibility checks; the pasting client imports the public root plus the
explicit non-Cartesian fixture `Test.RingedSpaceBaseChange`. Legacy clients
preserve their older import syntax rather than serving as native API examples.

Use `lake --wfail build RingedSpacesExamples` to check just the examples after
the cache fetch. `module`/`public import` is required for new downstream files;
`import all` appears only in the audit drivers to inspect intentionally private
declarations. Ordinary clients need only the documented public imports.

## Quick Start

`RingedSpacesExamples.lean` stores and compiles these examples with the
default build. For compatible full ringed-space morphisms on an indexed open
cover, gluing produces a unique global morphism:

```lean
module

public import RingedSpaces

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

example {X Y : RingedSpace.{u, u}} (C : RingedSpace.OpenCover X)
    (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) :
    ∃! global : X ⟶ Y, ∀ i, C.ι i ≫ global = f i :=
  C.existsUnique_gluing f hf
```

The stored module also checks literal-intersection compatibility and the
adjunction for arbitrary continuous inverse images of module presheaves.
For the module-sheaf functor, two-sided Hom inverse identities, naturality,
whole additive unit and both triangles, use the build-checked root-only
[`Test/SheafInverseImageRoot.lean`](Test/SheafInverseImageRoot.lean).
For arbitrary full-morphism structure maps, mates, module pushforward and
explicit right-tensor pullback, use the root-only
[`Test/RingedSpaceFullMorphismRoot.lean`](Test/RingedSpaceFullMorphismRoot.lean).

## API Documentation

[`docs/API.md`](docs/API.md) provides a historical source-only Markdown snapshot
of native Lean signatures and docstrings for 33 modules at source revision
`fc4581c6b42eb3b2c3dbeb714a8c76c51934d4fb` with doc-gen4
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`: 282 loaded public source
names and 281 native records. The previously published full-morphism snapshot
had 55 Lean files; the next published snapshot had 58; this tree has 62,
including the pasting leaf, public-root-plus-fixture client, constant-closed leaf
and root-only client. In particular,
the historical snapshot does **not** authenticate the present root,
`lakefile.toml` or whole source. [`docs/README.md`](docs/README.md) gives
the historical binding boundary and direct API map for the added sheaf and
full-morphism modules. The seven earlier mathematical guides explain their
constructions and proofs. No JavaScript, dependency website, fonts or
downloaded upstream assets are shipped. The historical API snapshot is not
a certification of the present tree or a source-coverage decision.
The coherence/base-change, pasting and constant-closed guides and their respective clients
describe and check the added API; they are **not** part of the historical
33-module API snapshot. On September 26, 2026, the originating incubator
implementation was accepted and integrated at
`93a5cfd0bfefac803b66fbd21aff7b346ad7fa54`; the destination transfer at
`20890358aa62cfbccaeb2a75fbac105fa2e469a3` separately received independent
review 3551. That exact-revision review is not owner destination acceptance,
release acceptance, publication or a source-coverage decision for that transfer.
The pasting promotion has separate destination review, owner acceptance and
publication records; this API description alone certifies none of those
decisions or source coverage.

On a 15 GiB Linux worker with `LEAN_NUM_THREADS=1`, a matching cache fetch
decompressed 8,892 mathlib artifacts; a historical incremental warning-fatal
default build after migration reported 2,216 Lake jobs without an out-of-memory event.
The initial download/decompression and cold local compilation can take several
minutes and vary with network, CPU and available memory. These figures describe
that environment and workload, not a time guarantee or a new benchmark.
Generated API pages, source and contributor credit, and artifact-specific
verification are described in `docs/API.md` and `NOTICE.md`.
