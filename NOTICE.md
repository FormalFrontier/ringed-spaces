# Attribution and redistribution

This library's original Lean development, examples, mathematical expositions,
README, metadata and this notice were prepared by Formal Frontier contributors
for distribution under the unmodified root Apache-2.0 `LICENSE`. Authorship
and an Apache license do not assert or identify a copyright owner. Atlas is
credited as the mathematical author and responsible maintainer of the
ringed-space development. The source-specific correspondence and research
records are not needed to use this library and are not redistributed here.

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
source-only Markdown adaptation of native declaration signatures and project
docstrings, using separately built `leanprover/doc-gen4` at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`. The shipped adapter in
`scripts/generate_api.py` credits Atlas's multivariate-polynomials and
quadratic-algebras recipes and Anchor's original ideal-completion recipe, all
project contributions under Apache-2.0. Native HTML, Lean `Init` output,
scripts/styles/fonts and the upstream debounce snippet are **not** shipped.
The doc-gen4 tool remains separately credited under its Apache-2.0 license;
no rights claim about its excluded generated-site assets is inferred.

The pooled Worker A and Worker B Git names identify contributions, not
copyright ownership. The following task names and UIDs distinguish the actual
contributors behind those names:

| Contribution | Task name | Task UID |
| --- | --- | --- |
| Indexed ringed-space gluing and comparison | `hive-request-944903a7858d6c222d80ac1dc46723d7b9bbff80` | `037dd975-e922-472a-94c9-f1d56edfc640` |
| Literal-intersection restriction bridge | `hive-request-7a762c41a2c0682a91c146ba2d9498e4ce8ed722` | `2d5e19df-ec66-4093-9e00-b2f2d9d7d6c5` |
| Full inverse-image ringed-space factorization | `hive-request-351325c8c7fd420f97d33934a3be741833cfa7aa` | `69f909bc-4062-4663-a601-d91d8b62d3ed` |
| Same-site module-presheaf and sheaf scalar extension | `hive-request-059c55871ebeddb1bccf9c10f1cbeea1988728ac` | `9a080541-5121-4c36-9714-1c2b234ac4ce` |
| Continuous inverse-image module presheaf | `hive-request-6361c8ed8605658db6d8006fc95ead297e4ab524` | `bb3a5f5e-d55a-4838-bb0b-172ffc0ef968` |
| Right-factor tensor symmetry | `hive-request-0ff101586d96db47643f8e5085129ef680eacba4` | `c88277e7-cabc-4f57-89f2-6cbca2fe981d` |
| Concrete inverse-image module-presheaf Hom adjunction | `hive-request-3654894e6d3a4c58515807835d3b7255676c4e5a` | `681f8868-9053-4c6c-8bed-0c9a38c0d56e` |
| Right-factor concrete client repair | `hive-request-d7ba5651f8efe840a23b6b47f136806c59e9fdc7` | `9bc91951-bf3b-4356-ab9e-ad394afb57a5` |
| Initial native module migration | `hive-request-77c44ba5698358cc1a5a8f95828d8e1b51e71214` | `8790fdd0-9915-4c08-9b58-b2718793885b` |
| Native pointwise reduction repair | `hive-request-1b0f87400764453ac4f2cffcbd679e1599ffd603` | `a79f5543-153a-422e-9fe1-9e2c79d5eb9f` |
| Remaining native migration and reader-facing assembly | `hive-request-63f2ca2d0bd718c788051e54bfe3979f1963ff9d` | `7339fe4d-df71-4a07-9d97-ea5f49d9618b` |
| First-release documentation, official license and source-only regeneration successor | `hive-request-41717f60bb4a91da5e3daa7d82ec28313c7d64fd` | `f4d10b9a-48f7-4b10-bdb8-92ca99f5152d` |
| Direct-import module-sheaf inverse-image library and test preparation (bounded owner acceptance, not release) | `hive-request-8f33afe07a3ab0de314522e27f4bbaec2df1940d` | `30841a63-6910-4c7d-8c48-ddb0f57c9b58` |
| Four-file frozen-candidate reader documentation and attribution only, not mathematical authorship | `hive-request-79238d2214e00adca3bc76cce1c1b6ea9eada4e7` | `4ce11a72-2e1f-474c-ba5c-79536d05a926` |
| Sheaf inverse-image root export, default-target preparation, root-only client and reader-status corrections, not new library mathematics (bounded preparation accepted September 26, 2026) | `hive-request-e1482775b6fa0022d03fbe4fdd5c2293fc7b3376` | `b3302f82-95f8-495a-bd02-d2be7d0a95e9` |
| Full ringed-space pushforward comparison (mathematical precursor, notice repair by Atlas; bounded preparation accepted September 26, 2026) | `hive-request-1851085fe7b35662d923a451caba91e82427e7c6` | `65354068-4250-4472-ae04-fbda63a4074a` |
| Explicit full ringed-space right-tensor pullback and adjunction (bounded preparation accepted September 26, 2026) | `hive-request-fc2cfe5450b0e4cddf69b3f460f342adcb40c54b` | `7d5af61a-1416-4194-9676-723f77b26c14` |
| Coherent sheaf/full-morphism root exports, complete defaults, root-only client and reader reconciliation, not new library mathematics (combined candidate assembled September 26, 2026) | `hive-request-0179a299c52c1f49a9763bece89e0fa96c822a36` | `7194f9b4-2354-4f6a-a0b4-92cbc42c5eda` |

Earlier source-repository research precursors, distinct from direct production
authorship, were contributed by Tasks
`hive-request-e55556273e3e7d75dd94de6a309a21d16dbd8bee`
(`000b2379-cdee-48dd-9d49-adb9c8a54597`),
`hive-request-ed585cec87f054b23a8f72d6c5882b0f6753bc73`
(`c4410aab-4878-47a4-aa7f-0e50bd436202`),
`hive-request-29cff68cea9e29fce4412766b7ed365b46113d1a`
(`fa3e8621-5869-468f-be90-761589ca692b`), and
`hive-request-a71657830db53cd29881f0026fa8b5e3d6a9ef3c`
(`a78a3887-0c81-4d19-9348-781caa1bce1c`). For the new module-sheaf
candidate specifically, `hive-request-ed585cec87f054b23a8f72d6c5882b0f6753bc73`
(`c4410aab-4878-47a4-aa7f-0e50bd436202`) worked on source module-action
research and `hive-request-a71657830db53cd29881f0026fa8b5e3d6a9ef3c`
(`a78a3887-0c81-4d19-9348-781caa1bce1c`) on presheaf Hom research;
`hive-request-724a310985250437cd65e489d2a64be08ee12871`
(`1e63d20e-3f1e-43da-8f6b-4f17e60020f4`) contributed sheaf-coherence
research and `hive-request-73dc549815be100a03dd91d507a98ee9f7e396cd`
(`c1aa7177-6bf6-4ff5-9a2b-8cdda8317c5d`) sheaf Hom research. These are
source-research precursors, not direct authorship of the new library leaves;
their ideas and proofs were adapted to an independent library. No source PDF
or scan is bundled. The direct-import native mathematics and prior reader
documentation received separate bounded owner preparation acceptances. Those
decisions do not themselves establish acceptance of the combined root/default-target
assembly, its integration, release or source coverage; these stages have separate
revision-specific decisions. Atlas subsequently corrected this assembly's status
language without changing its mathematical library content.
