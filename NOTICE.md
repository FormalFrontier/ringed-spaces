# Attribution and redistribution

This library's original Lean development, examples, mathematical expositions,
README, metadata and this notice were prepared by Formal Frontier contributors
for distribution under the unmodified root Apache-2.0 `LICENSE`. Authorship
and an Apache license do not assert or identify a copyright owner. Atlas
coordinates the mathematical design and maintains the ringed-space library;
original proofs, transfers, clients, documentation and independent review
have distinct contributors and roles. The source-specific correspondence
and research records are not needed to use this library and are not
redistributed here.

`RingedSpaces/OpenCover.lean` retains the authentic 2022 Andrew Yang copyright,
license and author notice from mathlib's
`Mathlib/AlgebraicGeometry/Gluing.lean`: its generic categorical transition-map
construction was adapted, not merely cited. The upstream file is distributed
under Apache-2.0 at mathlib commit
`83abb3e776bdefcbc447a1e44d0debe4010039e5` (see its retained header and
mathlib's license). The surrounding open-cover comparison and full-morphism
proofs are separate project developments. Other mathlib categories, sheaves,
Kan extensions, module colimits and tensor products are imported as the pinned
external dependency, not copied into this repository; their original mathlib
authorship remains with the upstream project. In particular, the native
varying-ring module-colimit API used here credits Joël Riou in mathlib.

The repository's root `LICENSE` is the complete Apache-2.0 license text.
`formalization.yaml` uses the publicly distributed Apache-2.0 v0.4
formalization.yaml schema and template as a metadata format, not as copied
mathematical text. The mathematical prose, tests and examples in this tree
are project contributions; historical raw checking output and internal
review records are not included in the shipped artifact. `docs/API.md` is a
navigation- and prose-adjusted historical Markdown adaptation of native
declaration signatures and project docstrings, using separately built
`leanprover/doc-gen4` at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`. The shipped adapter in
`scripts/generate_api.py` credits Atlas's multivariate-polynomials and
quadratic-algebras recipes and Anchor's original ideal-completion recipe, all
project contributions under Apache-2.0. Native HTML, Lean `Init` output,
scripts/styles/fonts and the upstream debounce snippet are **not** shipped.
The doc-gen4 tool remains separately credited under its Apache-2.0 license;
no rights claim about its excluded generated-site assets is inferred.

## Project contribution roles

Formal Frontier contributors used agent-assisted Lean development and native
kernel checking; the project independently reviews substantive mathematics,
APIs, rights and proof integrity. The pooled Git author names do not establish
sole mathematical authorship, copyright ownership or independent approval.
The roles below distinguish original work from its integration into this
standalone library; specific revision-bound contributor and review records
remain in the project's development history.

| Mathematics or artifact | Original and adapted contributions |
| --- | --- |
| Open restrictions, indexed gluing, literal intersections and full inverse-image factorization | Formal Frontier contributors developed the ringed-space proofs, intersection bridge and inverse-image construction; the generic gluing transition construction is an adaptation of Andrew Yang's credited mathlib work, not an original project invention. |
| Module presheaf/sheaf scalar extension, right-factor tensor symmetry and continuous presheaf inverse image | Original Formal Frontier proofs and client examples were subsequently maintained, migrated to the native module system and assembled into the public root. The underlying mathlib categories, sheaves and tensor products are dependencies rather than project-authored copies. |
| Continuous module-sheaf inverse image and bundled Hom adjunction | Earlier source research on module actions and Hom/coherence inspired independent library proofs, direct-import clients, a root export and reader guides. Research precursors and library authorship are distinct roles. |
| Full ringed-space module pushforward and explicit right-tensor pullback | Formal Frontier contributors developed the comparison and adjunction proofs and examples; separate contributors assembled the public exports, root-only clients and documentation. Joël Riou's varying-ring module-colimit and module-sheaf work remains credited to mathlib. |
| Pullback coherence and arbitrary-square mates | Source prototypes preceded the original reusable proof and client; a separate contributor transferred the accepted mathematics into this library, prepared public-root examples and documentation. A transfer does not claim original authorship. |
| Square-mate horizontal and vertical pasting | The original proof and clients were developed for a reusable incubator module; a separate destination contribution adapted the library module, fixture, root client and guide without claiming original proof authorship. |
| Constant-closed full morphisms and all-affine-map non-affineness | Original constructor, extension proofs and clients are distinguished from their subsequent destination transfers, public-root client adaptations and guides. |
| Documentation, license and native API adaptation | Documentation and native-module migration have separate contributors from the mathematical originals. Anchor originated the ideal-completion doc-generation recipe; Atlas adapted it for multivariate polynomials and quadratic algebras and maintains the project adapter. Independent reviewers verify exact candidate revisions but do not become their original authors. |

The historical [`docs/API.md`](docs/API.md) links to the matching official
published source snapshot; its original generator, manifest and generated
output have a separate exact-input binding. This adjusted reader page is not
new generation or a claim of complete current-API coverage. Neither this notice
nor metadata decides source correspondence or source-coverage status.
