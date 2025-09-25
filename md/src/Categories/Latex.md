
LaTeX Support in these Slides
===

These slides use the `showdown` cmarkdown overter with the `katex` extension to render Latex in html.

You can put code in a ````latex` block

```latex
\begin{aligned}
\mathcal{L}(y, f_1, \ldots, f_k) &= \sum_{i=1}^{n} \left( y_i - \sum_{j=1}^{k} f_j(x_i) \right)^2 \\
&= \sum_{i=1}^{n} \left( y_i - \left( f_1(x_i) + \cdots + f_k(x_i) \right) \right)^2 \\
&= \sum_{i=1}^{n} \left( y_i^2 - 2y_i\sum_{j=1}^{k} f_j(x_i) + \left( \sum_{j=1}^{k} f_j(x_i) \right)^2 \right) \\
&= \sum_{i=1}^{n} y_i^2 - 2\sum_{i=1}^{n} y_i \left( \sum_{j=1}^{k} f_j(x_i) \right) + \sum_{i=1}^{n} \left( \sum_{j=1}^{k} f_j(x_i) \right)^2
\end{aligned}
```

Or you can put it in a pair of dollar signs: $\sum_{k=1}^{n} k$ -- inline with your text.

Tikz
===

Sadly, `tikz` diagrams don't work. This might be because tools like katex and mathjax don't call a latex compiler.
Instead they seem to be parsing the latex and building the displayed formula from scratch.
So you can't just include the tikz package like you would in a native latex environment.

A path to `tikz` would be to

- Embped tikz in your lean file with a special delimiter like ````tikz`
- Covert the lean file to markdown using dm.py
- Extract all tikz blocks from the resulting markdown file and compile them using pdflatex or similar
- Relace the tikz blocks with \<img\> tags or \<svg\> tags



License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

