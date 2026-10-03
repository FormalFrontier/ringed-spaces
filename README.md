# Ringed Spaces

A Lean library of full ringed-space morphisms: open restrictions and gluing,
inverse-image factorization, and modules over changing sheaves of rings. It also
constructs ringed spaces of continuous functions and studies their stalks and
open immersions. The constructions reuse mathlib's sheaves, categorical
pullbacks and module functors; equalities of morphisms include their **sheaf
maps**, not just their maps of underlying spaces.

## Headline results

- **Restriction and indexed gluing.** For `X Y : RingedSpace.{u, u}`,
  [`RingedSpace.isPullback_restrictInf`](RingedSpaces/Restriction.lean) identifies
  the literal intersection of two opens with the pullback of their full
  restrictions. Compatible morphisms on any `J : Type u`-indexed open cover
  glue uniquely to a full morphism `X ⟶ Y`, also when `J` and `X` are empty;
  [`OpenCover.existsUnique_gluing_of_intersection`](RingedSpaces/OpenCover.lean)
  accepts literal-intersection compatibility.
- **Inverse-image factorization.** For `Y : RingedSpace.{u, u}` and a continuous
  map `g : T ⟶ Y.carrier`, `T : TopCat.{u}`,
  [`RingedSpace.inverseImage`](RingedSpaces/InverseImage.lean) has literal
  carrier `T` and mathlib's inverse-image ring sheaf. Every full `f : X ⟶ Y`
  factors through it by [`toInverseImage_ofInverseImage`](RingedSpaces/InverseImage.lean);
  this is *not* a categorical ringed-space fiber product.
- **Continuous-function spaces.** A topological commutative ring `R` gives a
  [`ContinuousFunctions.ringedSpace`](RingedSpaces/ContinuousFunctions.lean)
  with stalk evaluation and full maps induced by continuous maps; open
  embeddings give [ringed-space open immersions](RingedSpaces/ContinuousFunctions/OpenImmersion.lean).
  For a T1 topological field `K` with a topological division-ring structure,
  its stalks are local and the maps and open immersions are locally ringed.
  See the [continuous-functions guide](docs/continuous-functions.md).
- **Finite-regularity scalar functions.** For a charted space over a nontrivially
  normed field, [`FiniteRegularityFunctions.sheaf`](RingedSpaces/FiniteRegularityFunctions.lean)
  gives chosen-chart `C^r` scalar sections for `r : ℕ` and local stalks without
  an `IsManifold` or nonempty-carrier assumption. Smooth sections weaken to
  finite order; order zero is naturally isomorphic to the existing continuous
  scalar sheaf, including compatible stalk evaluation. Finite-`C^r` maps
  [pull sections back](RingedSpaces/FiniteRegularityFunctions/Maps.lean) and induce
  locally ringed-space morphisms compatible with identity, composition and
  both endpoint sheaf comparisons. For an open subtype with its induced charts,
  inclusion is an [open immersion](RingedSpaces/FiniteRegularityFunctions/OpenImmersion.lean)
  of locally ringed spaces; the restriction comparison satisfies both whole-arrow
  factorization equations. On a finite-order manifold with the self model
  `𝓘(𝕜, E)`, [`localBall`](RingedSpaces/FiniteRegularityFunctions/LocalBall.lean)
  restricts the chosen chart near any point to a diffeomorphism onto an entire
  positive-radius ball in the normed model space. Its locally ringed-space
  isomorphism identifies the restricted ambient scalar-function space with
  the ball's scalar-function space. See the
  [finite-regularity guide](docs/finite-regularity-functions.md).
- **Change of coefficient sheaves.** A full natural map of commutative-ring
  presheaves induces a tensor-presheaf/restriction-of-scalars adjunction;
  with the required site sheafification witnesses, a full map of ring sheaves
  gives the [sheafified adjunction](RingedSpaces/Modules/SheafChangeOfRings.lean).
  Right-factor tensor extension is naturally isomorphic to left-factor
  extension. See [scalar extension](docs/module-change-of-rings.md) and
  [right-factor symmetry](docs/change-of-rings-symmetry.md).
- **Continuous inverse images of modules.** Neighborhood-colimit module
  presheaf inverse image and its genuine sheafification have bundled linear
  Hom adjunctions to the corresponding native pushforwards, with whole
  additive-sheaf comparisons; the additive comparison alone does not provide
  coefficient transport. See the [presheaf](docs/presheaf-inverse-image-hom.md)
  and [sheaf](docs/sheaf-inverse-image.md) guides.
- **Full-morphism module functors.** For any full `f : X ⟶ Y`, the original
  ring-sheaf structure map defines module pushforward; explicit sheafified
  right-tensor pullback is its left adjoint, with a comparison to native
  pullback. Composition and identity comparisons and the push–pull mate of
  **any commutative square** satisfy horizontal and vertical pasting laws;
  no general invertibility of that mate is claimed. See the
  [pushforward](docs/ringed-space-pushforward.md),
  [pullback](docs/ringed-space-pullback.md),
  [coherence](docs/ringed-module-coherence-base-change.md) and
  [pasting](docs/ringed-module-base-change-pasting.md) guides.
- **Constant closed-point morphisms.** For a commutative local ring `R`, any
  ring map from `R` to global sections of a ringed space constructs a full
  morphism with constant closed-point base. For same-universe commutative
  `R, S`, `[Nontrivial S]`, and a map `alpha : R →+* S` sending an element
  of `IsLocalRing.maximalIdeal R` to a unit, this morphism `Spec S ⟶ Spec R`
  differs from **every** affine-induced full morphism. Neither construction
  asserts a scheme morphism. See the [constructor](docs/closed-point-hom.md)
  and [non-affineness](docs/closed-point-nonaffine.md) guides.

## Using the library

With access to the official GitHub repository, add the library to your
`lakefile.toml`:

```toml
[[require]]
name = "ringed-spaces"
git = "https://github.com/FormalFrontier/ringed-spaces.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves the latest release when
the dependency is first added or updated, and `lake-manifest.json` locks the
resolved commit until the next update. To pin a particular release instead,
replace `main` with a commit from its history.

Use the public aggregate import (or a narrower leaf listed below). This
complete example is already checked in [`RingedSpacesExamples.lean`](RingedSpacesExamples.lean):

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

The full restriction maps, their identity/composition laws, the cover
compatibility and gluing APIs, and the inverse-image sheaf mate are exposed
without unfolding definitions; the [`Restriction`](RingedSpaces/Restriction.lean),
[`OpenCover`](RingedSpaces/OpenCover.lean) and
[`InverseImage`](RingedSpaces/InverseImage.lean) modules give their signatures.
The [root-only examples](RingedSpacesTests/ContinuousFunctions.lean) and
[open-immersion clients](RingedSpacesTests/ContinuousFunctionsOpenImmersion.lean) show the
general-ring and field-specific continuous-function imports and local
open-immersion-instance recipe.

## Building

The `lean-toolchain` pins Lean `v4.34.0-rc2`; `lakefile.toml` pins mathlib to
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and `lake-manifest.json`
records the dependency graph. In a matching pinned build environment, fetch
the precompiled mathlib cache **before** building:

```sh
lake exe cache get && lake build
```

The default build includes the aggregate import, stored examples and shipped
tests. After the cache fetch, `lake build RingedSpacesExamples` checks just
the stored examples; `lake --wfail build` requests a stricter warning-fatal
check. The ordinary recipe does not suppress warnings or claim a warning-free
build. If the matching cache cannot be fetched, do not fall back to compiling
mathlib from source.

## Contents

`RingedSpaces` exports the leaves below. Import a leaf for a narrower API;
the linked guides supply definitions, formulas, hypotheses and clients.

| Module | Contents and guide |
| --- | --- |
| [`RingedSpaces.Restriction`](RingedSpaces/Restriction.lean) | Full open-restriction maps and intersection pullback. |
| [`RingedSpaces.OpenCover`](RingedSpaces/OpenCover.lean) | Arbitrary indexed covers and full-morphism gluing. |
| [`RingedSpaces.InverseImage`](RingedSpaces/InverseImage.lean) | Native-sheaf inverse image and full-morphism factorization. |
| [`RingedSpaces.ClosedPointHom`](RingedSpaces/ClosedPointHom.lean) | [Constant closed-point construction](docs/closed-point-hom.md). |
| [`RingedSpaces.ClosedPointNonAffine`](RingedSpaces/ClosedPointNonAffine.lean) | [Exclusion of every affine-induced map](docs/closed-point-nonaffine.md). |
| [`RingedSpaces.ContinuousFunctions`](RingedSpaces/ContinuousFunctions.lean) | [General-ring sheaf, evaluation and maps; field locality](docs/continuous-functions.md). |
| [`RingedSpaces.FiniteRegularityFunctions`](RingedSpaces/FiniteRegularityFunctions.lean) | [Finite-regularity scalar sections, stalks, and endpoint comparisons](docs/finite-regularity-functions.md). |
| [`RingedSpaces.FiniteRegularityFunctions.Maps`](RingedSpaces/FiniteRegularityFunctions/Maps.lean) | [Chosen-chart finite-regularity pullbacks and locally ringed-space maps](docs/finite-regularity-functions.md#maps-of-finite-regularity). |
| [`RingedSpaces.FiniteRegularityFunctions.OpenImmersion`](RingedSpaces/FiniteRegularityFunctions/OpenImmersion.lean) | [Finite-order scalar open-subtype immersions and restriction comparison](docs/finite-regularity-functions.md#open-subtypes-and-restriction). |
| [`RingedSpaces.ContinuousFunctions.OpenImmersion`](RingedSpaces/ContinuousFunctions/OpenImmersion.lean) | [General-ring open immersions and field restriction](docs/continuous-functions.md#open-embeddings-and-restriction). |
| [`RingedSpaces.Modules.PresheafChangeOfRings`](RingedSpaces/Modules/PresheafChangeOfRings.lean) | [Tensor presheaf and adjunction](docs/module-change-of-rings.md). |
| [`RingedSpaces.Modules.SheafChangeOfRings`](RingedSpaces/Modules/SheafChangeOfRings.lean) | [Sheafified tensor adjunction](docs/module-change-of-rings.md#sheaves). |
| [`RingedSpaces.Modules.PresheafChangeOfRingsSymmetry`](RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean) | [Right-/left-factor tensor comparison](docs/change-of-rings-symmetry.md). |
| [`RingedSpaces.Modules.SheafChangeOfRingsSymmetry`](RingedSpaces/Modules/SheafChangeOfRingsSymmetry.lean) | [Sheafified tensor symmetry](docs/change-of-rings-symmetry.md). |
| [`RingedSpaces.Modules.PresheafInverseImage`](RingedSpaces/Modules/PresheafInverseImage.lean) | [Continuous neighborhood-colimit inverse image](docs/presheaf-inverse-image.md). |
| [`RingedSpaces.Modules.PresheafInverseImageHom`](RingedSpaces/Modules/PresheafInverseImageHom.lean) | [Bundled presheaf Hom adjunction](docs/presheaf-inverse-image-hom.md). |
| [`RingedSpaces.Modules.SheafInverseImage`](RingedSpaces/Modules/SheafInverseImage.lean) | [Continuous sheaf inverse image](docs/sheaf-inverse-image.md). |
| [`RingedSpaces.Modules.SheafInverseImageHom`](RingedSpaces/Modules/SheafInverseImageHom.lean) | [Bundled sheaf Hom adjunction](docs/sheaf-inverse-image.md#adjunction). |
| [`RingedSpaces.Modules.RingedSpacePushforward`](RingedSpaces/Modules/RingedSpacePushforward.lean) | [Full-morphism module pushforward](docs/ringed-space-pushforward.md). |
| [`RingedSpaces.Modules.RingedSpacePullback`](RingedSpaces/Modules/RingedSpacePullback.lean) | [Explicit right-tensor module pullback](docs/ringed-space-pullback.md). |
| [`RingedSpaces.Modules.PullbackCoherence`](RingedSpaces/Modules/PullbackCoherence.lean) | [Identity and composition isomorphisms](docs/ringed-module-coherence-base-change.md). |
| [`RingedSpaces.Modules.BaseChange`](RingedSpaces/Modules/BaseChange.lean) | [Commutative-square push–pull mate](docs/ringed-module-coherence-base-change.md#square-comparison). |
| [`RingedSpaces.Modules.BaseChangePasting`](RingedSpaces/Modules/BaseChangePasting.lean) | [Horizontal and vertical pasting](docs/ringed-module-base-change-pasting.md). |

## Conventions and limitations

- Restriction, cover and inverse-image APIs use diagonal universes
  `RingedSpace.{u, u}`, `TopCat.{u}` and cover indices `J : Type u`; no
  mixed-universe lifting is asserted. The cover may be infinite or empty
  when its source space is empty; opens and intersections may be empty.
  These results need no local rings, schemes or nonzero coefficient rings.
- Change-of-rings presheaves allow independent universes for the site objects
  and morphisms, but share the coefficient and module-carrier universe.
  Generic ring/module sheaf scalar extension requires the three site
  witnesses detailed in the [change-of-rings guide](docs/module-change-of-rings.md#sheaves).
  Sheafified tensors are **genuine sheafifications**: an arbitrary open
  section need not be a raw sectionwise tensor.
- Continuous-function ringed spaces need only a topological commutative ring;
  stalk locality and locally ringed-space maps additionally require a T1
  topological field with a topological division-ring structure. Stalk maps
  go **backward** along continuous maps. For open subtypes, mathlib's
  `SheafedSpace.IsOpenImmersion.isoRestrict` compares general-ring objects;
  the library supplies the locally ringed-space comparison. The
  [guide](docs/continuous-functions.md#open-embeddings-and-restriction)
  gives the local `letI` recipe and both full restriction triangles.
- Arbitrary commutative squares yield a module push–pull mate and pasting,
  not a generally invertible comparison, a Cartesian/flatness theorem, or
  a raw-tensor formula on every open. Full ringed-space maps and inverse
  images do not imply locally ringed-space or scheme morphisms.
- [`docs/API.md`](docs/API.md) documents an **older 33-module snapshot**, not
  the complete present library or its authoritative current signatures.
  [`docs/README.md`](docs/README.md) explains the snapshot boundary and maps
  the later direct-import APIs to their guides and sources.

## References

- The [pinned mathlib dependency](lakefile.toml), including its
  [sheafed-space gluing](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Gluing.lean),
  sheaf-of-continuous-functions, inverse-image and module APIs.
- [Mathematical guides](docs/README.md#current-api-map-beyond-the-historical-snapshot)
  for constructions and current direct imports; the
  [continuous-functions guide](docs/continuous-functions.md) includes the
  general-ring/field boundary and full restriction equations.

## Credits and license

Authors: Formal Frontier Agents (agent-assisted Lean development). The
open-cover transition construction adapts Andrew Yang's mathlib work;
the continuous-function methods build on work by Kim Morrison, Andrew Yang,
Johan Commelin, Adam Topaz and Heather Macbeth. Other upstream mathlib
contributions, original project work, individual roles and retained
third-party notices are detailed in [`NOTICE.md`](NOTICE.md) and the Lean
module headers. Licensed under Apache-2.0; see [`LICENSE`](LICENSE).
