#!/usr/bin/python

import sys
import re

dont_show_deopt_state = True

def main():
    lines = sys.stdin.readlines()
    parsed_lines = []
    for l in lines:
        if l.strip().startswith('#'): continue
        match = re.match('([0-9]+)(.+)===([^\[]+)\[\[.*', l.strip())
        if match is not None:
            node_id = match.group(1)
            node_type = match.group(2).strip()
            node_inputs = filter(lambda x: len(x.strip()) != 0, match.group(3).split(' '))
            if dont_show_deopt_state:
                try:
                    begin = node_inputs.index('(')
                    end = node_inputs.index(')')
                    node_inputs[begin:(end + 1)] = []
                except ValueError:
                    pass
            parsed_lines.append((node_id, node_type, node_inputs))

    print "digraph G {"
    print "node [shape=record];"
    for (node_id, node_type, node_inputs) in parsed_lines:
        inputs = '|'.join(map(lambda i: '<i%d> %d' % (i, i), range(0, len(node_inputs))))
        edge_name = str(node_id) + ': ' + node_type
        vertical = '|'.join(map(lambda s: '{%s}' % s, [inputs, edge_name]))
        print '  ' + str(node_id) + '[label=\"{' + vertical + '}\"]'

    for (node_id, node_type, node_inputs) in parsed_lines:
        print '   %s -> %s:i0 [color="red"]' % (node_inputs[0], node_id)
        for idx,input in enumerate(node_inputs[1:]):
            print '   %s -> %s:i%d' % (input, node_id, idx + 1)
    print '}'

if __name__ == '__main__':
    main()
