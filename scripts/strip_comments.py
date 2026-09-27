#!/usr/bin/env python3
"""Print Coq sources with comments and strings blanked out, keeping line numbers."""
import sys


def strip(text: str) -> str:
    out = []
    i, n, depth, in_str = 0, len(text), 0, False
    while i < n:
        c = text[i]
        if in_str:
            if c == '"':
                if i + 1 < n and text[i + 1] == '"':  # escaped quote
                    out.append('  ')
                    i += 2
                    continue
                in_str = False
            out.append(c if c == '\n' else ' ')
            i += 1
        elif depth > 0:
            if text.startswith('(*', i):
                depth += 1
                out.append('  ')
                i += 2
            elif text.startswith('*)', i):
                depth -= 1
                out.append('  ')
                i += 2
            else:
                out.append(c if c == '\n' else ' ')
                i += 1
        elif text.startswith('(*', i):
            depth = 1
            out.append('  ')
            i += 2
        elif c == '"':
            in_str = True
            out.append(' ')
            i += 1
        else:
            out.append(c)
            i += 1
    return ''.join(out)


if __name__ == '__main__':
    for path in sys.argv[1:]:
        with open(path, encoding='utf-8') as f:
            sys.stdout.write(strip(f.read()))
