#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Adverse controls for the complete, source-bound native Markdown adapter."""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

import generate_api as api


def rejected(label, records, sources, inventory, hashes, edit):
    changed = copy.deepcopy(records)
    edit(changed)
    try:
        api.render(changed, sources, api.SOURCE, inventory, hashes)
    except ValueError:
        return label
    raise RuntimeError('incorrectly accepted corruption: ' + label)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-data', type=Path, required=True)
    parser.add_argument('--loaded-inventory', type=Path)
    args = parser.parse_args()
    if sys.flags.optimize:
        parser.error('optimized assertions are unsupported')
    root = Path(__file__).resolve().parent.parent
    sources = {path: (root / path).read_bytes() for path in api.INPUTS}
    paths = {module: args.native_data / ('declaration-data-' + module + '.bmp') for module in api.MODULES}
    records = {module: json.loads(path.read_bytes()) for module, path in paths.items()}
    hashes = {module: hashlib.sha256(path.read_bytes()).hexdigest() for module, path in paths.items()}
    if args.loaded_inventory:
        inventory = api.public_inventory(args.loaded_inventory.read_text())
    else:
        inventory = json.loads((root / 'docs/api-manifest.json').read_text())['loaded_public']
    markdown, manifest = api.render(records, sources, api.SOURCE, inventory, hashes)
    facts = json.loads(manifest)
    assert facts['api_sha256'] == hashlib.sha256(markdown).hexdigest()
    assert len(facts['public_declarations']) == 281 and len(facts['loaded_public']) == 282
    assert len(facts['missing_docstrings']) == 122 and not facts['missing_module_docs']
    assert len(facts['inputs']) == 36 and len(facts['native_record_sha256']) == 33
    assert all(('../' + module.replace('.', '/') + '.lean').encode() in markdown
               for module in api.MODULES)
    source_module = 'RingedSpaces.OpenCover'
    first = records[source_module]['declarations'][0]
    target = first['info']['name']
    controls = []
    edits = {
        'omitted-module': lambda data: data.pop(source_module),
        'omitted-declaration': lambda data: data[source_module]['declarations'].pop(),
        'duplicate-declaration': lambda data: data[source_module]['declarations'].append(
            copy.deepcopy(data[source_module]['declarations'][0])),
        'wrong-module-origin': lambda data: data[source_module].update(name='Wrong.Module'),
        'wrong-kind': lambda data: data[source_module]['declarations'][0]['info'].update(kind='axiom'),
        'wrong-source-scheme': lambda data: data[source_module]['declarations'][0]['info'].update(
            sourceLink='https:' + data[source_module]['declarations'][0]['info']['sourceLink'][len('git-source:'):]),
        'wrong-source-revision': lambda data: data[source_module]['declarations'][0]['info'].update(
            sourceLink=data[source_module]['declarations'][0]['info']['sourceLink'].replace(api.SOURCE, '0' * 40, 1)),
        'wrong-source-path': lambda data: data[source_module]['declarations'][0]['info'].update(
            sourceLink=data[source_module]['declarations'][0]['info']['sourceLink'].replace(
                'RingedSpaces/OpenCover.lean', 'RingedSpaces/Restriction.lean', 1)),
        'bad-self-link': lambda data: data[source_module]['declarations'][0]['info'].update(docLink='wrong'),
        'zero-line': lambda data: data[source_module]['declarations'][0]['info'].update(line=0),
        'other-valid-line': lambda data: data[source_module]['declarations'][0]['info'].update(
            line=data[source_module]['declarations'][0]['info']['line'] + 1),
        'boolean-line': lambda data: data[source_module]['declarations'][0]['info'].update(line=True),
        'active-header': lambda data: data[source_module]['declarations'][0].update(header='<script>bad</script>'),
        'unsafe-header': lambda data: data[source_module]['declarations'][0].update(
            header=data[source_module]['declarations'][0]['header'].replace('theorem', 'unsafe theorem', 1)),
    }
    for label, edit in edits.items():
        controls.append(rejected(label, records, sources, inventory, hashes, edit))
    bad_inventory = dict(inventory)
    del bad_inventory[target]
    try:
        api.render(records, sources, api.SOURCE, bad_inventory, hashes)
    except ValueError:
        controls.append('omitted-loaded-name')
    else:
        raise RuntimeError('incorrectly accepted omitted loaded name')
    changed_sources = dict(sources)
    changed_sources['RingedSpaces/OpenCover.lean'] += b'\n'
    try:
        api.bind_sources(api.SOURCE, changed_sources, manifest)
    except ValueError:
        controls.append('modified-committed-source')
    else:
        raise RuntimeError('incorrectly accepted changed committed source')
    assert len(controls) == 16
    print(json.dumps({'status': 'passed', 'controls': controls,
                      'public_native': 281, 'missing_docstrings': 122,
                      'api_sha256': facts['api_sha256'], 'release_acceptance': False}, indent=2))


if __name__ == '__main__':
    main()
