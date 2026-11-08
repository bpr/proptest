#!/bin/bash
# Check the book's code. Run from the repository root:
#   pixi run book-test [book/src/PAGE.md ...]
#
# - Every ```mojo block must be a complete program: its lines starting with
#   `~` (hidden in the book; see book.toml) are unhidden, and the result is
#   compiled and run, and must exit successfully. Blocks importing
#   proptest_numojo also get extras/ and NuMojo ($NUMOJO_PARENT, default
#   ../MojoDEC/third_party) on the include path.
# - ```mojo-sig blocks (signatures in the reference) aren't programs. The
#   names they declare (`name(` or `name[` at the start of a line, and
#   `trait`/`struct` names) are imported from proptest, so each must exist.
set -u
root=$(pwd)
numojo_parent=$(realpath -m "${NUMOJO_PARENT:-../MojoDEC/third_party}")
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
pages=("$@")
if [ ${#pages[@]} -eq 0 ]; then
    mapfile -t pages < <(find book/src -name '*.md' | sort)
fi
failed=0
total=0
run() {  # run FILE LABEL [extra mojo flags...]
    local f=$1 label=$2
    shift 2
    total=$((total + 1))
    if (cd "$out" && PROPTEST_DATABASE=none mojo run -I "$root" "$@" "$f" > "$f.log" 2>&1); then
        echo "ok    $label"
    else
        failed=$((failed + 1))
        echo "FAIL  $label"
        sed 's/^/      /' "$f.log" | head -30
    fi
}
for page in "${pages[@]}"; do
    base=$(echo "$page" | sed 's|^book/src/||; s|/|_|g; s|\.md$||')
    # ```mojo block N -> $out/<base>_N.mojo, with the `~` markers removed;
    # names declared in ```mojo-sig blocks -> $out/<base>.names
    awk -v dir="$out" -v base="$base" '
        /^```mojo[[:space:]]*$/ { kind = "mojo"; n++; file = dir "/" base "_" n ".mojo"; printf "" > file; next }
        /^```mojo-sig[[:space:]]*$/ { kind = "sig"; next }
        /^```/ && kind != "" { if (kind == "mojo") close(file); kind = ""; next }
        kind == "mojo" { sub(/^~/, ""); print > file; next }
        kind == "sig" {
            line = $0
            sub(/^[[:space:]]+/, "", line)
            decl = 0
            if (line ~ /^(trait|struct) /) { sub(/^(trait|struct) /, "", line); decl = 1 }
            if (match(line, /^[A-Za-z_][A-Za-z0-9_]*[\[(:]/)) {
                name = substr(line, 1, RLENGTH - 1)
                last = substr(line, RLENGTH, 1)
                if ((last != ":" || decl) && name !~ /^(def|comptime|len|print|range)$/)
                    print name > (dir "/" base ".names")
            }
        }
    ' "$page"
    for f in "$out/${base}"_*.mojo; do
        [ -e "$f" ] || continue
        label="$page ($(basename "$f"))"
        if ! grep -q '^def main' "$f"; then
            total=$((total + 1))
            failed=$((failed + 1))
            echo "FAIL  $label: not a complete program (no main; hide the missing lines with ~)"
            rm "$f"
            continue
        fi
        if grep -q 'proptest_numojo' "$f"; then
            run "$f" "$label" -I "$root/extras" -I "$numojo_parent"
        else
            run "$f" "$label"
        fi
        rm -f "$f" "$f.log"
    done
    if [ -e "$out/$base.names" ]; then
        names=$(sort -u "$out/$base.names" | paste -sd, -)
        f="$out/${base}_names.mojo"
        printf 'from proptest import %s\n\ndef main():\n    pass\n' "$names" > "$f"
        run "$f" "$page (declared names: $names)"
        rm -f "$f" "$f.log" "$out/$base.names"
    fi
done
echo "$((total - failed)) of $total checks passed"
[ $failed -eq 0 ]
