// highlight.js has no Mojo grammar; Mojo's syntax is close enough to
// Python's for its highlighting. book.js highlights before this script
// runs, so register the aliases and highlight the Mojo blocks again.
// (highlight.js keeps the markup already in a block, such as the spans
// that hide lines.) `mojo-sig` blocks are signatures in the reference.
(function () {
    if (typeof hljs === "undefined") return;
    hljs.registerAliases(["mojo", "mojo-sig"], { languageName: "python" });
    document
        .querySelectorAll("code.language-mojo, code.language-mojo-sig")
        .forEach(function (block) {
            hljs.highlightBlock(block);
        });
})();
