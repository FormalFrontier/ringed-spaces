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

The library uses **diagonal universes** `X Y : RingedSpace.{u,u}`, `T : TopCat.{u}`
and, for covers, `J : Type u`. No mixed-universe lifting is claimed. No local-ring, scheme,
finite-cover, nonempty-cover, nonempty-member, or nonzero-ring hypothesis is
required. The index family may be empty when `X` is empty; see
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

The default build includes the library, the stored examples and every `Test`
module, including concrete boundary clients and private/full-origin axiom
audits. Use `lake --wfail build RingedSpacesExamples` to check just the examples
after the cache fetch. `module`/`public import` is required for new downstream
files; `import all` appears only in the audit drivers to inspect intentionally
private declarations. Ordinary clients need only the documented public imports.

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

## API Documentation

[`docs/API.md`](docs/API.md) provides source-only Markdown generated from
native Lean signatures and docstrings for all 33 shipped Lean modules.
[`docs/README.md`](docs/README.md) explains exact input, tool and manifest
bindings, regeneration, declared documentation gaps and source links. No
JavaScript, dependency website, fonts or downloaded upstream assets are shipped.
The four mathematical guides under `docs/` explain complex constructions and
proofs; the generated signatures complement rather than replace them.

On a 15 GiB Linux worker with `LEAN_NUM_THREADS=1`, a matching cache fetch
decompressed 8,892 mathlib artifacts; an incremental warning-fatal default
build after migration reported 2,216 Lake jobs without an out-of-memory event.
The initial download/decompression and cold local compilation can take several
minutes and vary with network, CPU and available memory. These figures describe
that environment and workload, not a time guarantee or a new benchmark.
Generated API pages, source and contributor credit, and artifact-specific
verification are described in `docs/API.md` and `NOTICE.md`.
