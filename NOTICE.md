# Attribution and redistribution

Formal Frontier contributors prepared this library's original Lean development,
examples, mathematical expositions, README, metadata and this notice for
distribution under the unmodified root Apache-2.0 `LICENSE`. Authorship and an
Apache license do not assert or identify a copyright owner. Atlas maintains the
ringed-space library; mathematical proofs, examples and documentation have
distinct contributors. Source-specific correspondence and research records are
not part of this library.

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

`RingedSpaces/ContinuousFunctions.lean` and
`RingedSpaces/ContinuousFunctions/OpenImmersion.lean` retain the upstream
copyright notices for Kim Morrison (2020) and Heather Macbeth (2023),
their Apache-2.0 notice and adaptation credit. The sheaf and continuous-function
methods build on work by Kim Morrison, Andrew Yang, Johan Commelin, Adam Topaz
and other mathlib contributors; the stalk and open-subtype approaches adapt
Heather Macbeth's methods. Formal Frontier contributors developed and extended
the reusable mathematical proofs, concrete examples and unified guide. These
contributions do not claim to originate the upstream mathematics or own its
copyright.

`RingedSpaces/FiniteRegularityFunctions.lean` retains Heather Macbeth's
authentic 2023 copyright notice and credits Adam Topaz alongside Formal
Frontier contributors. Its finite-order sheaf and local-stalk arguments adapt
the Apache-2.0 mathlib smooth-sheaf work of Macbeth and Topaz, while its
endpoint comparisons reuse mathlib's smooth scalar sheaf and this library's
continuous-function sheaf. The chosen-chart finite-order results and their
concrete examples are separate library developments; this attribution does not
assert copyright ownership.

The repository's root `LICENSE` is the complete Apache-2.0 license text.
`formalization.yaml` uses the publicly distributed Apache-2.0 v0.4
formalization.yaml schema and template as a metadata format, not as copied
mathematical text. The mathematical prose, tests and examples in this tree are
project contributions. `docs/API.md` is a
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

## Mathematical and software attribution

Formal Frontier contributors used agent-assisted Lean development and kernel
checking. Pooled Git author names do not establish sole mathematical authorship
or copyright ownership. The contributions below distinguish original work from
adaptations and imported dependencies.

| Mathematics or artifact | Original and adapted contributions |
| --- | --- |
| Open restrictions, indexed gluing, literal intersections and full inverse-image factorization | Formal Frontier contributors developed the ringed-space proofs, intersection bridge and inverse-image construction; the generic gluing transition construction is an adaptation of Andrew Yang's credited mathlib work, not an original project invention. |
| Module presheaf/sheaf scalar extension, right-factor tensor symmetry and continuous presheaf inverse image | Formal Frontier contributors proved the scalar-extension and inverse-image results and supplied examples, native modules and public-root exports. The underlying mathlib categories, sheaves and tensor products are imported dependencies, not project-authored copies. |
| Continuous module-sheaf inverse image and bundled Hom adjunction | Formal Frontier contributors developed library proofs, direct-import examples and reader guides informed by earlier research on module actions and Hom/coherence. |
| Full ringed-space module pushforward and explicit right-tensor pullback | Formal Frontier contributors proved the comparisons and adjunction and prepared examples, public exports and documentation. Joël Riou's varying-ring module-colimit and module-sheaf work remains credited to mathlib. |
| Pullback coherence and arbitrary-square mates | Formal Frontier contributors proved the reusable coherence results, adapted earlier mathematical prototypes and prepared public-root examples and documentation. |
| Square-mate horizontal and vertical pasting | Formal Frontier contributors proved the pasting laws and supplied the library module, fixture, public-root examples and guide; earlier proof prototypes are distinct contributions. |
| Constant-closed full morphisms and all-affine-map non-affineness | Formal Frontier contributors supplied the constructor, extension proofs, examples and guide. |
| Continuous-function sheaves, evaluation, ringed and locally ringed-space maps, and open immersions | Mathlib contributors' sheaf and open-subtype methods are retained and credited in both Lean modules. Formal Frontier contributors proved the extensions and supplied concrete examples and a standalone guide. |
| Finite-order scalar-function sheaves and endpoint comparisons | Heather Macbeth and Adam Topaz's smooth-sheaf methods inform the chosen-chart construction; Formal Frontier contributors developed the finite-order section, stalk and comparison proofs and concrete clients while reusing the existing smooth and continuous sheaves. |
| Documentation, license and native API adaptation | Documentation and native-module work include contributions distinct from the mathematical originals. Anchor originated the ideal-completion doc-generation recipe; Atlas adapted it for multivariate polynomials and quadratic algebras and maintains the project adapter. |

The historical [`docs/API.md`](docs/API.md) reflects its original source
snapshot rather than the complete current API. Its adapted Markdown prose is
not new generation or a claim of source coverage.
