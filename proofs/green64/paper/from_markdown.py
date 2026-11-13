#!/usr/bin/env python3
"""Regenerate article sections, preserving every Markdown math node verbatim."""
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
DOCS = HERE.parent / 'docs'
CHAPTERS = ['proof', 'weights', 'correlation', 'bilinear', 'marked-correlation', 'physical-lift',
            'forest-moments', 'local-energy',
            'congruences', 'block-sieve', 'rectangles', 'sieve', 'lean-guide']


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def text(inlines):
    parts = []
    for node in inlines:
        if node['t'] == 'Str':
            parts.append(node['c'])
        elif node['t'] in ('Space', 'SoftBreak', 'LineBreak'):
            parts.append(' ')
        elif node['t'] == 'Code':
            parts.append(node['c'][1])
    return ''.join(parts)


def sha(payload):
    return hashlib.sha256(payload).hexdigest()


def keep_headings(blocks, baselines):
    """Reserve space before Pandoc emits a heading's PDF destination."""
    result = []
    for block in blocks:
        if block.get('t') == 'Header' and block['c'][0] > 1:
            result.append({'t': 'RawBlock', 'c': [
                'latex', rf'\Needspace{{{baselines}\baselineskip}}']})
        result.append(block)
    return result


def main():
    documents, sources, before_math = {}, {}, Counter()
    for chapter in CHAPTERS:
        source = DOCS / (chapter + '.md')
        raw = source.read_bytes()
        doc = json.loads(subprocess.check_output(
            ['pandoc', '--from=markdown', '--to=json'], input=raw))
        documents[chapter] = doc
        sources[source.name] = sha(raw)
        before_math.update(node['c'][1] for node in nodes(doc) if node.get('t') == 'Math')

    # Stable internal destinations replace links between the Markdown chapters.
    anchors = set()
    for chapter, doc in documents.items():
        for node in nodes(doc):
            if node.get('t') == 'Header':
                level, attr, inlines = node['c']
                attr[0] = chapter if level == 1 else chapter + '-' + attr[0]
                anchors.add(attr[0])
                if inlines and inlines[0]['t'] == 'Str':
                    first = inlines[0]['c']
                    if re.fullmatch(r'\d+\.', first):
                        del inlines[0]
                        if inlines and inlines[0]['t'] == 'Space':
                            del inlines[0]

    for chapter, doc in documents.items():
        for node in list(nodes(doc)):
            if node.get('t') == 'Link':
                target = node['c'][2][0]
                filename, _, fragment = target.partition('#')
                label = text(node['c'][1])
                if filename.endswith('.lean') and re.fullmatch(r'[A-Za-z0-9_/.-]+', label):
                    node['c'][1] = [{'t': 'RawInline', 'c': ['latex',
                        r'\nolinkurl{' + label + '}']}]
                if filename in {name + '.md' for name in CHAPTERS}:
                    stem = filename.removesuffix('.md')
                    fragment = re.sub(r'^\d+[-.]', '', fragment)
                    anchor = stem + ('-' + fragment if fragment else '')
                    assert anchor in anchors, (chapter, target, anchor)
                    node['c'][2][0] = '#' + anchor
                    if text(node['c'][1]).endswith('.md'):
                        node['c'][1] = [{'t': 'RawInline', 'c': ['latex',
                            r'Section~\ref{' + anchor + '}']}]
            elif node.get('t') == 'Code':
                content = node['c'][1]
                assert '{' not in content and '}' not in content, content
                node.clear()
                node.update(t='RawInline', c=['latex', r'{\small\nolinkurl{' + content + '}}'])

    sections = HERE / 'sections'
    sections.mkdir(exist_ok=True)
    correspondence = []
    after_math = Counter()
    products = {}
    for chapter, doc in documents.items():
        blocks = doc['blocks']
        cut = next((i for i, block in enumerate(blocks)
                    if block.get('t') == 'Header' and text(block['c'][2]) in
                    {'Source correspondence', 'Correspondence with Lean'}), None)
        if cut is not None:
            moved = blocks[cut:]
            heading = moved[0]
            heading['c'][0] = 2
            heading['c'][2] = copy.deepcopy(blocks[0]['c'][2])
            correspondence.extend(moved)
            doc['blocks'] = blocks[:cut]
        doc['blocks'] = keep_headings(doc['blocks'], 6)
        after_math.update(node['c'][1] for node in nodes(doc) if node.get('t') == 'Math')
        output = subprocess.check_output(
            ['pandoc', '--from=json', '--to=latex', '--no-highlight', '--wrap=auto'],
            input=json.dumps(doc).encode()).decode()
        output = re.sub(r'This\s+file', 'This section', output)
        output = re.sub(r'the present\s+file', 'the present section', output)
        output = output.replace('in the Markdown', 'in the exposition')
        (sections / (chapter + '.tex')).write_text(output)
        products[chapter + '.tex'] = sha(output.encode())

    doc = copy.deepcopy(documents['proof'])
    doc['blocks'] = [{'t': 'Header', 'c': [1, ['source-correspondence', [], []],
                        [{'t': 'Str', 'c': 'Further source correspondence'}]]}] + keep_headings(correspondence, 10)
    after_math.update(node['c'][1] for node in nodes(doc) if node.get('t') == 'Math')
    assert before_math == after_math, 'Mathematical content changed during conversion'
    output = subprocess.check_output(
        ['pandoc', '--from=json', '--to=latex', '--no-highlight', '--wrap=auto'],
        input=json.dumps(doc).encode()).decode()
    (sections / 'source-correspondence.tex').write_text(output)
    products['source-correspondence.tex'] = sha(output.encode())
    receipt = {'source_sha256': sources, 'generated_sha256': products,
               'math_nodes_preserved': sum(before_math.values()),
               'math_payloads_equal': True,
               'scope': 'Conversion preserves the Markdown mathematics; it is not a Lean proof audit.'}
    (HERE / 'CONVERSION.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'chapters': len(CHAPTERS), 'math_nodes_preserved': sum(before_math.values())}))


if __name__ == '__main__':
    main()
