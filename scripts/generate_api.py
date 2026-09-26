#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Render complete pinned native signatures and docstrings as source-only Markdown.

This adapter is based on Atlas's accepted multivariate-polynomials and
quadratic-algebras source-only recipes, ultimately derived from Anchor's
ideal-completion work. Acceptance of those tools does not accept this result.
"""

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parent.parent
TOOL = '97d4ecdfc8e09e7f511724c25e303d448de6a3db'
SOURCE = 'fc4581c6b42eb3b2c3dbeb714a8c76c51934d4fb'
SOURCE_TREE = 'c330aa042beae57328c5428193f2bfa5c4ff336d'
SOURCE_IDENTIFIER = 'git-source:' + SOURCE
MODULES = (
    'RingedSpaces', 'RingedSpaces.InverseImage',
    'RingedSpaces.Modules.PresheafChangeOfRings',
    'RingedSpaces.Modules.PresheafChangeOfRingsSymmetry',
    'RingedSpaces.Modules.PresheafInverseImage',
    'RingedSpaces.Modules.PresheafInverseImageHom',
    'RingedSpaces.Modules.SheafChangeOfRings',
    'RingedSpaces.Modules.SheafChangeOfRingsSymmetry',
    'RingedSpaces.OpenCover', 'RingedSpaces.Restriction', 'RingedSpacesExamples',
    'Test.Axioms', 'Test.ChangeOfRingsSymmetry',
    'Test.ChangeOfRingsSymmetryAxioms', 'Test.ChangeOfRingsSymmetryFixture',
    'Test.ChangeOfRingsSymmetryRoot', 'Test.InverseImage',
    'Test.ModuleChangeOfRings', 'Test.ModuleChangeOfRingsAxioms',
    'Test.ModuleChangeOfRingsRoot', 'Test.OpenCover', 'Test.PresheafInverseImage',
    'Test.PresheafInverseImageAxioms', 'Test.PresheafInverseImageConcrete',
    'Test.PresheafInverseImageHom', 'Test.PresheafInverseImageHomAxioms',
    'Test.PresheafInverseImageHomConcrete', 'Test.PresheafInverseImageHomRoot',
    'Test.PresheafInverseImageLegacyAggregate',
    'Test.PresheafInverseImageNativeDirect', 'Test.PresheafInverseImageRoot',
    'Test.Restriction', 'Test.Root',
)
INPUTS = tuple(module.replace('.', '/') + '.lean' for module in MODULES) + (
    'lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
HIDDEN_RECURSOR = 'AlgebraicGeometry.RingedSpace.OpenCover.rec'
KINDS = {
    'theorem': {'theorem'},
    'def': {'def', 'noncomputable def', 'abbrev', 'noncomputable abbrev'},
    'ctor': {'constructor'},
    'structure': {'structure'},
    'instance': {'instance', 'noncomputable instance'},
}
GUIDES = {
    'RingedSpaces.Modules.PresheafChangeOfRings': 'module-change-of-rings.md',
    'RingedSpaces.Modules.PresheafChangeOfRingsSymmetry': 'change-of-rings-symmetry.md',
    'RingedSpaces.Modules.PresheafInverseImage': 'presheaf-inverse-image.md',
    'RingedSpaces.Modules.PresheafInverseImageHom': 'presheaf-inverse-image-hom.md',
    'RingedSpaces.Modules.SheafChangeOfRings': 'module-change-of-rings.md',
    'RingedSpaces.Modules.SheafChangeOfRingsSymmetry': 'change-of-rings-symmetry.md',
}


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(*arguments, cwd=ROOT):
    return subprocess.check_output(['git', '--no-replace-objects', *arguments], cwd=cwd)


class Header(HTMLParser):
    """Retain native header text, including all displayed implicit arguments."""

    def __init__(self, html):
        super().__init__(convert_charrefs=True)
        self.stack, self.text, self.kinds, self.names = [], [], [], []
        self.feed(html)
        self.close()
        require(not self.stack, 'unclosed native header')

    def handle_starttag(self, tag, attributes):
        require(tag in {'div', 'span', 'a'}, 'unexpected native header tag')
        attrs = dict(attributes)
        require(not any(key.startswith('on') for key in attrs), 'active native header attribute')
        if tag == 'div' and 'decl_type' in attrs.get('class', '').split():
            self.text.append(' ')
        self.stack.append((tag, set(attrs.get('class', '').split())))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, 'unbalanced native header')
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), 'text outside native header')
        self.text.append(value)
        if any('decl_kind' in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any('decl_name' in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError('unexpected native header comment')

    def handle_decl(self, _):
        raise ValueError('unexpected native header declaration')

    def rendered(self):
        return ' '.join(''.join(self.text).split())


def module_doc(data):
    docs = re.findall(r'/-!(.*?)\-/', data.decode(), re.S)
    require(len(docs) <= 1 and all('/-' not in doc for doc in docs),
            'unsupported module documentation envelope')
    return docs[0].strip() if docs else ''


def public_inventory(text):
    declarations = {}
    artifacts = set()
    for line in text.splitlines():
        if line.startswith('ARTIFACT|'):
            _, module, _ = line.split('|', 2)
            require(module not in artifacts, 'duplicate inventoried module')
            artifacts.add(module)
        elif line.startswith('DECL|'):
            _, module, name, kind, *fields = line.split('|')
            values = dict(field.split('=', 1) for field in fields)
            if (values['private'], values['auto'], values['internal']) == ('false', 'false', 'false') and values['range'] != 'none':
                require(name not in declarations, 'duplicate public name in loaded inventory')
                declarations[name] = {'module': module, 'kind': kind, 'range': values['range']}
    require(artifacts == set(MODULES) and len(declarations) == 282,
            'loaded module/public inventory differs')
    return declarations


def native_rows(records, sources, revision):
    require(re.fullmatch(r'[0-9a-f]{40}', revision) is not None and revision == SOURCE,
            'unknown source revision')
    require(set(records) == set(MODULES) and set(sources) == set(INPUTS),
            'incomplete shipped module/source input inventory')
    rows = []
    for module in MODULES:
        record = records[module]
        require(record['name'] == module, 'native module identity differs')
        path = module.replace('.', '/') + '.lean'
        for entry in record['declarations']:
            info = entry['info']
            name, kind = info['name'], info['kind']
            require(kind in KINDS and not any(item['name'] == name for item in rows),
                    'duplicate or unexpected native public kind')
            require(info['sourceLink'] == SOURCE_IDENTIFIER + '/' + path,
                    'stale or incorrect native source identifier: ' + name)
            require(unquote(info['docLink']) == './' + module.replace('.', '/') + '.html#' + name,
                    'incorrect native declaration link: ' + name)
            line = info['line']
            require(type(line) is int and 0 < line <= len(sources[path].splitlines()),
                    'invalid native source line: ' + name)
            header = Header(entry['header'])
            display_kind = ''.join(header.kinds).strip()
            require(''.join(header.names) == name and display_kind in KINDS[kind],
                    'native signature identity/kind mismatch: ' + name)
            text = header.rendered()
            require(not text.startswith(('unsafe ', 'partial ')) and '```' not in text,
                    'unsafe/partial or unsupported signature: ' + name)
            doc = info['doc'].strip()
            require('```' not in doc, 'unsupported docstring fence: ' + name)
            rows.append({'name': name, 'kind': kind, 'module': module,
                         'line': line, 'signature': text, 'doc': doc})
    require(len(rows) == 281, 'native public declaration count differs')
    return rows


def render(records, sources, revision, inventory, native_hashes):
    rows = native_rows(records, sources, revision)
    found = {row['name']: row for row in rows}
    require(set(found) | {HIDDEN_RECURSOR} == set(inventory),
            'native output lost or added public names')
    require(inventory[HIDDEN_RECURSOR]['module'] == 'RingedSpaces.OpenCover'
            and inventory[HIDDEN_RECURSOR]['kind'] == 'recursor',
            'unaccounted generated recursor')
    for name, row in found.items():
        require(inventory[name]['module'] == row['module'], 'wrong loaded module origin')
        actual = inventory[name]['kind']
        require((actual, row['kind']) in {
            ('definition', 'def'), ('theorem', 'theorem'),
            ('constructor', 'ctor'), ('inductive', 'structure'),
            ('definition', 'instance')}, 'native/loaded kind mismatch: ' + name)
        line = int(inventory[name]['range'].split(':', 1)[0])
        if name == 'AlgebraicGeometry.RingedSpace.OpenCover.mk':
            line = int(inventory['AlgebraicGeometry.RingedSpace.OpenCover']['range'].split(':', 1)[0])
        require(row['line'] == line, 'native/loaded source line mismatch: ' + name)
    absent_docs = [row['name'] for row in rows if not row['doc']]
    absent_modules = [module for module in MODULES if not module_doc(sources[module.replace('.', '/') + '.lean'])]
    lines = [
        '# Generated API reference', '',
        'Native source-only signatures for all 33 shipped Lean modules (281 recorded',
        'public declarations), with their complete original nonempty docstrings,',
        'relative links to all 33 module sources and explicit missing-doc accounting.',
        'The generated `OpenCover.rec` has no native record. See the',
        '[mathematical overview](../README.md),',
        '[module guides](README.md) and [exact artifact manifest](api-manifest.json).', '',
        'Signatures preserve native displayed implicit arguments, but contain no',
        'proof bodies. Native display may suppress type annotations on literals;',
        'consult the linked Lean source for elaborated declarations. No external',
        'JavaScript, fonts, dependency website or build cache is bundled.', '',
    ]
    for module in MODULES:
        path = module.replace('.', '/') + '.lean'
        lines.extend(['## Module `' + module + '`', ''])
        doc = module_doc(sources[path])
        if doc:
            lines.extend(['\n'.join('> ' + piece if piece else '>' for piece in doc.splitlines()), ''])
        else:
            lines.extend(['*No module-level docstring is attached in the Lean source.*', ''])
        lines.extend(['[Module source](../' + path + ')', ''])
        if module in GUIDES:
            lines.extend(['[Mathematical guide](' + GUIDES[module] + ')', ''])
        ordered = sorted((row for row in rows if row['module'] == module),
                         key=lambda row: (row['line'], row['name']))
        for row in ordered:
            lines.extend(['### `' + row['name'] + '`', '', '```lean', row['signature'], '```', ''])
            if row['doc']:
                lines.extend([row['doc'], ''])
            else:
                lines.extend(['*No declaration docstring is attached in the native record.*', ''])
            lines.extend([f"[Source](../{path}#L{row['line']}) (line {row['line']}).", ''])
    markdown = ('\n'.join(lines).rstrip('\n') + '\n').encode()
    manifest = {
        'format': 1, 'generator': 'scripts/generate_api.py',
        'generator_sha256': digest(Path(__file__).read_bytes()),
        'docgen_revision': TOOL, 'analyzed_source_revision': revision,
        'analyzed_source_tree': SOURCE_TREE, 'modules': list(MODULES),
        'source_identifier': SOURCE_IDENTIFIER,
        'inputs': {path: digest(sources[path]) for path in sorted(sources)},
        'loaded_public': inventory, 'public_declarations': [row['name'] for row in rows],
        'missing_native_name': HIDDEN_RECURSOR, 'missing_docstrings': absent_docs,
        'missing_module_docs': absent_modules,
        'native_record_sha256': native_hashes,
        'api_sha256': digest(markdown), 'proof_certification': False,
    }
    return markdown, (json.dumps(manifest, ensure_ascii=False, indent=2, sort_keys=True) + '\n').encode()


def bind_sources(revision, sources, generated_manifest):
    top = git('rev-parse', '--show-toplevel').decode().strip()
    require(Path(top).resolve() == ROOT, 'generator must run at its own Git root')
    kind = subprocess.run(['git', '--no-replace-objects', 'cat-file',
                           '--batch-check=%(objecttype)'], cwd=ROOT,
                          input=(revision + '\n').encode(), capture_output=True, check=True).stdout
    if kind == b'commit\n':
        require(git('rev-parse', revision + '^{tree}').decode().strip() == SOURCE_TREE,
                'source snapshot tree differs')
        for path, data in sources.items():
            require(git('show', revision + ':' + path) == data, 'source/pin drift: ' + path)
        return 'exact-git-object'
    require(kind == (revision + ' missing\n').encode(), 'present but wrong source object')
    committed = git('show', 'HEAD:docs/api-manifest.json')
    require((ROOT / 'docs/api-manifest.json').read_bytes() == committed,
            'uncommitted binding manifest')
    require(generated_manifest == committed, 'native/source/manifest binding differs')
    require(git('show', 'HEAD:scripts/generate_api.py') == Path(__file__).read_bytes(),
            'generator differs from parentless release commit')
    for path, data in sources.items():
        require(git('show', 'HEAD:' + path) == data, 'source/pin differs from release commit')
    return 'committed-parentless-manifest'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-data', required=True, type=Path)
    parser.add_argument('--source-revision', required=True)
    parser.add_argument('--loaded-inventory', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(args.source_revision == SOURCE, 'unsupported analyzed source revision')
    paths = git('ls-tree', '-r', '--name-only', 'HEAD').decode().splitlines()
    actual_modules = {path.removesuffix('.lean').replace('/', '.') for path in paths if path.endswith('.lean')}
    require(actual_modules == set(MODULES), 'candidate shipped module inventory differs')
    sources = {path: (ROOT / path).read_bytes() for path in INPUTS}
    native_files = {module: args.native_data / ('declaration-data-' + module + '.bmp') for module in MODULES}
    records = {module: json.loads(path.read_bytes()) for module, path in native_files.items()}
    native_hashes = {module: digest(path.read_bytes()) for module, path in native_files.items()}
    if args.loaded_inventory:
        inventory = public_inventory(args.loaded_inventory.read_text())
    else:
        committed = json.loads(git('show', 'HEAD:docs/api-manifest.json'))
        inventory = committed['loaded_public']
    markdown, manifest = render(records, sources, args.source_revision, inventory,
                                native_hashes)
    binding = bind_sources(args.source_revision, sources, manifest)
    for name, data in [('API.md', markdown), ('api-manifest.json', manifest)]:
        destination = ROOT / 'docs' / name
        if args.check:
            require(destination.read_bytes() == data, 'generated output differs: ' + name)
            require(git('show', 'HEAD:docs/' + name) == data,
                    'uncommitted generated output: ' + name)
        else:
            destination.write_bytes(data)
    print(json.dumps({'status': 'matched' if args.check else 'generated',
                      'source_binding': binding, 'shipped_modules': len(MODULES),
                      'public_native': 281, 'missing_docstrings': len(json.loads(manifest)['missing_docstrings']),
                      'api_sha256': digest(markdown), 'release_acceptance': False}))


if __name__ == '__main__':
    main()
