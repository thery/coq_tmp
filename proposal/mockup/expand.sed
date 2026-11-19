# shorthand of the hand-written HTML mock-ups -> HTML
s/>>/<\/span>/g
s/{v|\([^}]*\)}/<span class="formula var"><span class="m">\1<\/span><\/span>/g
s/{h|\([^}]*\)}/<span class="formula hyp"><span class="m">\1<\/span><\/span>/g
s/{c|\([^}]*\)}/<span class="formula claim"><span class="m">\1<\/span><\/span>/g
s/{f|\([^}]*\)}/<span class="formula fact"><span class="m">\1<\/span><\/span>/g
s/{m|\([^}]*\)}/<span class="m">\1<\/span>/g
s/{bm|\([^}]*\)}/<span class="by"><span class="m">\1<\/span><\/span>/g
s/{b|\([^}]*\)}/<span class="by"><code>\1<\/code><\/span>/g
s/{n|\([^}]*\)}/<span class="name">(<code>\1<\/code>)<\/span>/g
s/<<\([^:]*\):/<span class="p" data-id="\1">/g
s/{EX|\([^|]*\)|\([^}]*\)}/<h2><code>\1<\/code> <small>\2<\/small><\/h2>/g
