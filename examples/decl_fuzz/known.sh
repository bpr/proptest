#!/bin/bash
# Sourced by the oracles. known_crash BUILD LOG prints the issue number of
# the filed crash in known_crashes.txt (next to this file) that LOG, a
# crashed build's output, matches; nothing if none does, or if
# DECL_FUZZ_NO_KNOWN is set.
KNOWN_CRASHES="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/known_crashes.txt"

known_crash() {  # build log
    [ -n "$DECL_FUZZ_NO_KNOWN" ] && return
    local issue build pattern
    while read -r issue build pattern; do
        case "$issue" in '' | '#'*) continue ;; esac
        if [ "$build" = "$1" ] && grep -qE -- "$pattern" "$2"; then
            echo "$issue"
            return
        fi
    done < "$KNOWN_CRASHES"
}
