#!/usr/bin/env python3
"""Source checks for the Lean library (run by scripts/check.sh).

1. Every `.lean` file is a Lean module (first token after comments is `module`).
2. No forbidden directive occurs in code (comments and docstrings are ignored): `sorry`, `admit`, `axiom`,
   `native_decide`, `implemented_by`, `extern`, `unsafe`, `debug.skipKernelTC`, `maxHeartbeats`, `maxRecDepth`.
"""
import pathlib
import re
import sys

FORBIDDEN = re.compile(r'\b(?:sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|debug\.skipKernelTC|'
                       r'maxHeartbeats|maxRecDepth)\b')


def strip_comments(s: str) -> str:
    out = []
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c == '"':  # string literal
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            out.append(s[i:j + 1]); i = j + 1
        elif c == "'" and i + 2 < n and (s[i + 2] == "'" or (s[i + 1] == '\\' and "'" in s[i + 2:i + 8])):
            j = s.index("'", i + 2 if s[i + 1] != '\\' else i + 3)
            out.append(s[i:j + 1]); i = j + 1
        elif s.startswith('--', i):
            j = s.find('\n', i)
            i = n if j < 0 else j
        elif s.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if s.startswith('/-', j):
                    depth += 1; j += 2
                elif s.startswith('-/', j):
                    depth -= 1; j += 2
                else:
                    j += 1
            if depth:
                raise ValueError('unterminated block comment')
            out.append(' '); i = j
        else:
            out.append(c); i += 1
    return ''.join(out)


def main() -> None:
    root = pathlib.Path(__file__).resolve().parents[1]
    files = sorted(p for p in root.rglob('*.lean') if '.lake' not in p.parts)
    bad = []
    for p in files:
        code = strip_comments(p.read_text())
        if not code.split() or code.split()[0] != 'module':
            bad.append(f'{p.relative_to(root)}: not a module')
        for no, line in enumerate(code.splitlines(), 1):
            if FORBIDDEN.search(line):
                bad.append(f'{p.relative_to(root)}:{no}: {line.strip()}')
    print('\n'.join(bad) if bad else f'source checks OK ({len(files)} Lean files)')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
